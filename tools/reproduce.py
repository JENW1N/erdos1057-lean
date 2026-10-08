#!/usr/bin/env python3
"""Rebuild the frozen modular proof in a new directory; never edit its sources.

The portable full build has not been executed by the publication task.
--check-sources performs file/hash/order checks only and never invokes Lean.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


FLAGS = ["--trust=0", "-Dweak.google.answer=always_true", "-DElab.async=false"]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def inside(root, relative):
    path = Path(relative)
    require(not path.is_absolute() and ".." not in path.parts,
            f"Invalid relative source path: {relative}")
    resolved = (root / path).resolve()
    require(resolved.is_relative_to(root.resolve()), f"Source escapes root: {relative}")
    return resolved


def check_sources(root):
    meta = read(root / "tools/reproduction-inputs.json")
    require(meta["schema"] == 1, "Unsupported reproduction metadata schema")
    hashes = dict(meta["auxiliary_sha256"])
    groups = {}
    all_names = set()
    for group in ("baseline", "modular"):
        order = read(root / group / "source-order.json")
        require(order["schema"] == 1, f"Unsupported {group} order schema")
        rows = order["modules"]
        require(len(rows) == meta["module_counts"][group], f"Wrong {group} module count")
        seen = set()
        names = {row["module"] for row in rows}
        require(len(names) == len(rows), f"Duplicate module in {group}")
        require(not (all_names & names), "Baseline/custom module name overlap")
        for row in rows:
            require(not (set(row["dependencies"]) & names) - seen,
                    f"Dependency order error: {row['module']}")
            require(row["path"] not in hashes, f"Duplicate source path: {row['path']}")
            hashes[row["path"]] = row["sha256"]
            seen.add(row["module"])
        all_names.update(names)
        groups[group] = rows
    for relative, expected in hashes.items():
        path = inside(root, relative)
        require(path.is_file(), f"Missing source: {relative}")
        require(sha(path) == expected, f"Source hash mismatch: {relative}")
    manifest = read(root / "baseline/formal-conjectures/lake-manifest.json")
    require(manifest["packagesDir"] == ".lake/packages", "Unexpected package directory")
    packages = manifest["packages"]
    require(len({p["name"] for p in packages}) == len(packages), "Duplicate package")
    for package in packages:
        require(package["type"] == "git" and package.get("subDir") is None,
                f"Unsupported dependency layout: {package['name']}")
        require(re.fullmatch(r"[A-Za-z0-9_-]+", package["name"]), "Unsafe package name")
        require(re.fullmatch(r"[0-9a-f]{40}", package["rev"]), "Dependency is not commit-pinned")
        require(package["url"].startswith("https://github.com/"), "Unexpected dependency URL")
    mathlib = [p for p in packages if p["name"] == "mathlib"]
    require(len(mathlib) == 1 and mathlib[0]["rev"] == meta["mathlib_commit"], "Mathlib pin mismatch")
    toolchain = (root / "baseline/formal-conjectures/lean-toolchain").read_text().strip()
    require(toolchain == meta["lean_toolchain"], "Toolchain pin mismatch")
    return meta, groups, hashes, packages


def executable(value):
    # Do not resolve symlinks: Elan shims depend on argv[0] being lean or lake.
    found = shutil.which(value)
    require(found is not None, f"Executable not found: {value}")
    return os.path.abspath(found)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).absolute().parent.parent)
    parser.add_argument("--check-sources", action="store_true",
                        help="Verify source hashes and order only; no network or Lean")
    parser.add_argument("--lean", default="lean", help="Pinned Lean executable or Elan shim")
    parser.add_argument("--lake", default="lake", help="Lake from the same toolchain")
    parser.add_argument("--build-dir", type=Path, help="New, nonexistent output directory")
    args = parser.parse_args()
    root = args.root.resolve()
    meta, groups, hashes, packages = check_sources(root)
    print(json.dumps({"status": "SOURCE_CHECK_PASS", "files": len(hashes),
                      "baseline_modules": len(groups["baseline"]),
                      "proof_modules": len(groups["modular"]),
                      "lean_invoked": False}), flush=True)
    if args.check_sources:
        return 0

    lean, lake = executable(args.lean), executable(args.lake)
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    run = (args.build_dir or root / ".reproduction" / ("run-" + stamp)).absolute()
    require(not run.exists(), "Build directory must not exist; each run starts fresh")
    run.mkdir(parents=True, exist_ok=False)
    logs = run / "logs"
    logs.mkdir()
    frozen = run / "source"
    for relative, expected in hashes.items():
        target = frozen / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(inside(root, relative), target)
        require(sha(target) == expected, f"Copy drift: {relative}")
    deps = frozen / "baseline/formal-conjectures"
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN_OPTS"):
        env.pop(key, None)
    env["PATH"] = str(Path(lean).parent) + os.pathsep + env.get("PATH", "")
    env["LEAN_NUM_THREADS"] = "1"
    env["LEAN_ABORT_ON_PANIC"] = "1"
    result = {"status": "RUNNING", "started_utc": stamp, "root": str(root),
              "run": str(run), "commands": [], "source_hashes": hashes,
              "lean_commit_required": meta["lean_commit"], "flags": FLAGS,
              "worker_count_claimed": False, "official_platform_acceptance": False}
    write(run / "result.json", result)

    def command(argv, label, cwd=deps, command_env=None):
        log = logs / (label + ".log")
        started = time.monotonic()
        with log.open("wb") as stream:
            process = subprocess.run(argv, cwd=cwd, env=command_env or env,
                                     stdout=stream, stderr=subprocess.STDOUT, check=False)
        row = {"command": argv, "cwd": str(cwd), "exit_code": process.returncode,
               "seconds": time.monotonic() - started, "log": str(log.relative_to(run)),
               "log_sha256": sha(log)}
        result["commands"].append(row)
        write(run / "result.json", result)
        require(process.returncode == 0, f"Command failed; see {log}")
        return log.read_text(encoding="utf-8", errors="replace")

    def verify_packages(label):
        require(sha(deps / "lake-manifest.json") ==
                hashes["baseline/formal-conjectures/lake-manifest.json"], "Lake manifest changed")
        package_dir = deps / ".lake/packages"
        actual = {p.name for p in package_dir.iterdir() if p.is_dir()}
        require(actual == {p["name"] for p in packages}, "Unexpected dependency checkout")
        for package in packages:
            checkout = package_dir / package["name"]
            head = command(["git", "rev-parse", "HEAD"], label + "-head-" + package["name"], checkout).strip()
            require(head == package["rev"], f"Dependency HEAD drift: {package['name']}")
            dirty = command(["git", "status", "--porcelain", "--untracked-files=all"],
                            label + "-status-" + package["name"], checkout).strip()
            require(not dirty, f"Dependency source changed: {package['name']}")

    try:
        commit = command([lean, "--githash"], "lean-commit").strip()
        require(commit == meta["lean_commit"], "Wrong Lean compiler commit")
        result["lean_version"] = command([lean, "--version"], "lean-version").strip()
        result["lake_version"] = command([lake, "--version"], "lake-version").strip()
        for package in packages:
            checkout = deps / ".lake/packages" / package["name"]
            checkout.mkdir(parents=True, exist_ok=False)
            name = package["name"]
            command(["git", "init", "--quiet"], "init-" + name, checkout)
            command(["git", "remote", "add", "origin", package["url"]], "remote-" + name, checkout)
            command(["git", "fetch", "--no-tags", "--depth=1", "origin", package["rev"]],
                    "fetch-" + name, checkout)
            command(["git", "checkout", "--detach", package["rev"]], "checkout-" + name, checkout)
        verify_packages("before-build")
        # No update command and no cache downloads. Build the exact dependency tree.
        command([lake, "--no-cache", "build", "@mathlib/Mathlib"], "build-mathlib")
        verify_packages("after-build")
        lake_commit = command([lake, "env", "lean", "--githash"], "lake-lean-commit").strip()
        require(lake_commit == meta["lean_commit"], "Lake selected another Lean compiler")

        objects = run / "objects"
        objects.mkdir()
        package_paths = [deps / ".lake/packages" / p["name"] / ".lake/build/lib/lean"
                         for p in packages]
        proof_env = dict(env, LEAN_PATH=os.pathsep.join(map(str, [objects, *package_paths])))

        def compile_source(source, module, prefix, source_root):
            destination = objects / (module.replace(".", "/") + ".olean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            print(prefix + " " + module, flush=True)
            text = command([lean, *FLAGS, "-R", str(source_root), "-o", str(destination), str(source)],
                           prefix + "-" + module, source_root, proof_env)
            require(destination.exists(), f"Missing object: {module}")
            if prefix == "proof":
                require(not re.search(r"declaration uses .sorry.", text), f"Admitted declaration: {module}")

        for row in groups["baseline"]:
            compile_source(frozen / row["path"], row["module"], "baseline", deps)
        compile_source(frozen / "baseline/TaskSupport.lean", "TaskSupport", "support", frozen / "baseline")
        for row in groups["modular"]:
            compile_source(frozen / row["path"], row["module"], "proof", frozen / "modular/src")
        audit = frozen / meta["audit_source"]
        text = command([lean, *FLAGS, str(audit)], "audit-target", audit.parent, proof_env)
        matches = re.findall(r"'Bounty\.target' depends on axioms: \[([^\]]*)\]", text)
        require(len(matches) == 1, "Missing or ambiguous target axiom report")
        axioms = [name.strip() for name in matches[0].split(",") if name.strip()]
        require(set(axioms) <= set(meta["allowed_axioms"]), f"Unexpected axioms: {axioms}")
        require(not re.search(r"declaration uses .sorry.", text), "Audit contains an admitted declaration")
        verify_packages("final")
        for relative, expected in hashes.items():
            require(sha(frozen / relative) == expected, f"Frozen source changed: {relative}")
        check_sources(root)
        result.update(status="MODULAR_REBUILD_AND_TARGET_AUDIT_PASS", target_axioms=axioms,
                      completed_utc=dt.datetime.now(dt.timezone.utc).isoformat(),
                      standalone_file_validated=False, official_platform_acceptance=False)
        write(run / "result.json", result)
        print(json.dumps({"status": result["status"], "receipt": str(run / "result.json")}), flush=True)
        return 0
    except BaseException as error:
        result.update(status="NOT_PASSED", error=str(error),
                      completed_utc=dt.datetime.now(dt.timezone.utc).isoformat())
        write(run / "result.json", result)
        raise


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print("ERROR: " + str(error), file=sys.stderr)
        raise SystemExit(1)
