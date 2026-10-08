# Reproduce the modular proof

The historical modular build and target audit passed in the recorded environment. **This portable clean-build recipe has not been executed.** Its Python syntax and source-only checks were tested; those checks are not a new proof verification.

Requirements: Python 3.10 or later, Git, network access to the pinned GitHub dependencies, a working Lean/Lake toolchain `leanprover/lean4:v4.35.0-rc2`, and that toolchain's native build prerequisites. The required Lean commit is `11acb17ec6b07a8f9e9173e6845197929540936b`.

From the repository root, check the copied sources without invoking Lean or accessing the network:

```sh
python3 tools/reproduce.py --check-sources
```

Run a clean build in a new output directory:

```sh
python3 tools/reproduce.py --build-dir /absolute/path/to/new-build-directory
```

If necessary, select the matching Lean and Lake executables explicitly:

```sh
python3 tools/reproduce.py \
  --lean /path/to/toolchain/bin/lean \
  --lake /path/to/toolchain/bin/lake \
  --build-dir /absolute/path/to/new-build-directory
```

The script copies the exact sources into that new directory, fetches every dependency at the commit recorded in `baseline/formal-conjectures/lake-manifest.json`, and builds Mathlib locally with Lake's cache downloads disabled. It does not run `lake update`. It refuses dependency revision changes, dirty dependency sources, a changed manifest, or a different Lean commit. Mathlib is pinned to `065356127b1dc0016f66b7283ce0ce2c4055aa55`; the manifest pins the other eight packages.

It then compiles the 189 copied Formal Conjectures baseline modules, `TaskSupport.lean`, and the 320 proof modules in the recorded dependency order. Each compilation uses a fresh object directory with `--trust=0 -Dweak.google.answer=always_true -DElab.async=false`. Finally, the unchanged `verification/AuditTarget.lean` checks the exact challenge type and rejects every axiom except `propext`, `Classical.choice`, and `Quot.sound`.

The output directory contains `result.json` and command logs. Only `MODULAR_REBUILD_AND_TARGET_AUDIT_PASS` reports successful completion. Errors leave `NOT_PASSED` or the last incomplete receipt for inspection. Source checks alone print `SOURCE_CHECK_PASS`. The script records `LEAN_NUM_THREADS=1`; it does not claim that this measures or sets the Lean CLI's effective worker count.

The baseline sources already contain the official challenge corrections. Their source tree derives from Formal Conjectures base commit `7d1a8c9912747679d0093f6d1216420c33ee5ffa` plus the recorded audit patch; the resulting local commit `4b69a7dca3e731dd1f28cb523b9ebd2ea32527f4` need not be available from the public upstream repository.

This recipe checks the modular proof. It does not compile the standalone candidate, run a prize-platform submission, establish platform size compliance, or certify acceptance. Historical absolute paths and binary hashes remain in the separately preserved extraction evidence; this recipe creates fresh logs and receipts for the current machine.
