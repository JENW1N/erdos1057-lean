#!/usr/bin/env python3
"""Build the frozen October 9 standalone source and audit it in a fresh directory.

Use --dependency-root for an existing checkout containing .lake/packages at the
locked commits. Without it, public dependencies and their Mathlib cache are fetched.
The proof and Formal Conjectures baseline are always compiled from source.
"""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
from reproduce import check_sources, executable, inside, read, require, sha, write


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--build-dir', type=Path, help='New, nonexistent output directory')
    ap.add_argument('--dependency-root', type=Path, help='Pinned dependency checkout with .lake/packages')
    ap.add_argument('--lean', default='lean')
    ap.add_argument('--lake', default='lake')
    ap.add_argument('--threads', type=int, default=8)
    ap.add_argument('--check-sources', action='store_true')
    ap.add_argument('--external-sandbox', action='store_true', help='Caller supplies isolation; required off macOS')
    args = ap.parse_args()
    root = Path(__file__).resolve().parent.parent
    meta, groups, hashes, packages = check_sources(root)
    source = read(root / 'standalone/source.json')
    hashes.update({'standalone/Challenge.lean': source['source_sha256'],
                   'standalone/Audit.lean': source['audit_sha256']})
    for rel, expected in hashes.items():
        require(sha(inside(root, rel)) == expected, 'Source hash mismatch: ' + rel)
    require(args.threads > 0, '--threads must be positive')
    print(json.dumps({'status':'SOURCE_CHECK_PASS', 'standalone_sha256':source['source_sha256'], 'files':len(hashes)}), flush=True)
    if args.check_sources:
        return 0
    lean, lake = executable(args.lean), executable(args.lake)
    toolchain = Path(lean).resolve().parent.parent
    require(subprocess.check_output([lean, '--githash'], text=True).strip() == meta['lean_commit'], 'Wrong Lean commit')
    stamp = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    run = (args.build_dir or root / '.reproduction' / ('standalone-' + stamp)).resolve()
    require(not run.exists(), 'Use a new build directory')
    run.mkdir(parents=True)
    for name in ('logs','source','objects','home','tmp'):
        (run/name).mkdir()
    frozen, objects = run/'source', run/'objects'
    for row in groups['baseline']:
        target = frozen/row['path']; target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root/row['path'], target)
    for src, dst in [('baseline/TaskSupport.lean','baseline/TaskSupport.lean'),
                     ('standalone/Challenge.lean','Challenge.lean'),('standalone/Audit.lean','Audit.lean')]:
        target=frozen/dst; target.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(root/src,target)
    env={'PATH':str(Path(lean).parent)+os.pathsep+'/usr/bin:/bin', 'HOME':str(run/'home'),
         'TMPDIR':str(run/'tmp'), 'LANG':'en_US.UTF-8', 'LEAN_NUM_THREADS':str(args.threads),
         'LEAN_ABORT_ON_PANIC':'1', 'GIT_TERMINAL_PROMPT':'0', 'GIT_CONFIG_NOSYSTEM':'1'}
    result={'status':'RUNNING','started_utc':stamp,'source_sha256':source['source_sha256'],
            'compiler_sha256':sha(lean),'commands':[],'dependencies':[],
            'baseline_built_from_source':True,'proof_built_from_source':True,
            'official_acceptance':False}
    prefix=[]
    def command(label, argv, cwd=frozen, isolated=True):
        log=run/'logs'/(label+'.log'); start=time.monotonic()
        cmd=(prefix if isolated else [])+list(map(str,argv))
        print('START '+label,flush=True)
        with log.open('wb') as stream:
            proc=subprocess.run(cmd,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
        result['commands'].append({'label':label,'argv':cmd,'cwd':str(cwd),'exit_code':proc.returncode,
                                   'seconds':round(time.monotonic()-start,3),'log':str(log.relative_to(run)),
                                   'log_sha256':sha(log)})
        write(run/'result.json',result)
        require(proc.returncode==0, 'Failed '+label+'; see '+str(log))
        return log.read_text(errors='replace')
    try:
        if args.dependency_root:
            deps=args.dependency_root.resolve()
        else:
            deps=run/'dependencies';deps.mkdir()
            for name in ('lakefile.toml','lake-manifest.json','lean-toolchain'):
                shutil.copyfile(root/'baseline/formal-conjectures'/name,deps/name)
            for p in packages:
                d=deps/'.lake/packages'/p['name'];d.mkdir(parents=True)
                command('init-'+p['name'],['git','init','--quiet'],d,False)
                command('remote-'+p['name'],['git','remote','add','origin',p['url']],d,False)
                command('fetch-'+p['name'],['git','fetch','--no-tags','--depth=1','origin',p['rev']],d,False)
                command('checkout-'+p['name'],['git','checkout','--detach',p['rev']],d,False)
            command('mathlib-cache',[lake,'exe','cache','get'],deps,False)
        for p in packages:
            d=deps/'.lake/packages'/p['name']
            head=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip()
            require(head==p['rev'],'Wrong dependency commit: '+p['name'])
            dirty=subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],text=True).strip()
            require(not dirty,'Changed dependency source: '+p['name'])
            result['dependencies'].append({'name':p['name'],'commit':head,'tracked_source_clean':True,
                                           'cache':'existing pinned cache' if args.dependency_root else 'downloaded Mathlib cache'})
        env['LEAN_PATH']=os.pathsep.join(map(str,[objects,*[deps/'.lake/packages'/p['name']/'.lake/build/lib/lean' for p in packages]]))
        if sys.platform=='darwin' and not args.external_sandbox:
            sandbox=shutil.which('sandbox-exec');require(sandbox,'sandbox-exec unavailable')
            profile='(version 1)\n(allow default)\n(deny network*)\n(deny file-write*)\n(deny file-read* (subpath "/Users"))\n(deny file-read* (subpath "/private/var/folders"))\n(deny file-read* (subpath "/private/tmp"))\n(allow file-read-metadata)\n'
            for p in [run,toolchain,*[deps/'.lake/packages'/p['name'] for p in packages]]:
                profile+='(allow file-read* (subpath '+json.dumps(str(p.resolve()))+'))\n'
            profile+='(allow file-write* (subpath '+json.dumps(str(run))+'))\n(allow file-write* (literal "/dev/null"))\n'
            (run/'sandbox.sb').write_text(profile);prefix=[sandbox,'-f',str(run/'sandbox.sb')]
            result['isolation']='macOS sandbox-exec; no network, writes confined to run, user-home content denied except pinned toolchain/dependencies'
        else:
            require(args.external_sandbox,'Run in an isolated environment and pass --external-sandbox off macOS')
            result['isolation']='caller-supplied; this program has not verified external isolation'
        write(run/'environment.json',env)
        command('lean-version',[lean,'--version'])
        flags=['--trust=0','-Dweak.google.answer=always_true','-DElab.async=true','-j'+str(args.threads)]
        for i,row in enumerate(groups['baseline']):
            target=objects/(row['module'].replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
            command(f'baseline-{i:03}',[lean,*flags,'-R',frozen/'baseline/formal-conjectures','-o',target,frozen/row['path']])
        command('TaskSupport',[lean,*flags,'-R',frozen/'baseline','-o',objects/'TaskSupport.olean',frozen/'baseline/TaskSupport.lean'])
        command('Challenge',[lean,'--json',*flags,'--profile','-o',objects/'Challenge.olean',frozen/'Challenge.lean'])
        output=command('Audit',[lean,'--trust=0',frozen/'Audit.lean'])
        expected="'Bounty.target' depends on axioms: [propext, Classical.choice, Quot.sound]"
        require(expected in output, 'Missing expected axiom report')
        require(sha(frozen/'Challenge.lean')==source['source_sha256'],'Source changed during build')
        command('kernel-replay',[str(Path(lean).parent/'leanchecker'),'--verbose','Challenge'])
        result.update(status='SOURCE_BUILD_AUDIT_AND_KERNEL_REPLAY_PASS',completed_utc=dt.datetime.now(dt.timezone.utc).isoformat(),
                      target_axioms=['propext','Classical.choice','Quot.sound'],olean_sha256=sha(objects/'Challenge.olean'))
    except BaseException as exc:
        result.update(status='FAILED',error=str(exc));raise
    finally:
        write(run/'result.json',result)
    print(json.dumps({'status':result['status'],'receipt':str(run/'result.json')}),flush=True)
    return 0

if __name__=='__main__':
    raise SystemExit(main())
