from pathlib import Path
import concurrent.futures as cf, datetime as dt, hashlib, json, os, shutil, subprocess, tarfile, io, time
R=Path(__file__).resolve().parent;P=R.parent/'proof1057';N=R.parent/'verification1057';S=R/'source';O=R/'objects'
PIN='55fe0f1cd4d8e63b417eb122067ab3e307b39f32';TC=Path('/Users/jenwin/.elan/toolchains/leanprover--lean4---v4.35.0-rc2')
for n in ['source','objects','logs','home','tmp']: (R/n).mkdir(exist_ok=True)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def save(): (R/'result.json').write_text(json.dumps(result,indent=2)+'\n')
# Extract immutable public proof and baseline sources into this separate run.
blob=subprocess.check_output(['git','archive',PIN,'baseline','modular','verification/AuditTarget.lean','tools/reproduction-inputs.json'],cwd=P)
with tarfile.open(fileobj=io.BytesIO(blob)) as t:
 for m in t.getmembers():
  assert not m.name.startswith('/') and '..' not in Path(m.name).parts and not m.issym() and not m.islnk()
 t.extractall(S)
orders={k:json.loads((S/k/'source-order.json').read_text())['modules'] for k in ['baseline','modular']}
for rows in orders.values():
 for row in rows:assert sha(S/row['path'])==row['sha256']
assert len(orders['baseline'])==189 and len(orders['modular'])==320
# Reuse only the baseline objects freshly built earlier in this same audit.
(R/'baseline-receipt-at-copy.json').write_bytes((N/'result.json').read_bytes())
base_receipt=json.loads((R/'baseline-receipt-at-copy.json').read_text())
base_ok={r['label'] for r in base_receipt['commands'] if r['exit_code']==0}
for i,row in enumerate(orders['baseline']):
 assert f'baseline-{i:03}' in base_ok
 assert (S/row['path']).read_bytes()==(N/'source'/row['path']).read_bytes()
 rel=Path(row['module'].replace('.','/')+'.olean');(O/rel).parent.mkdir(parents=True,exist_ok=True);
 for artifact in (N/'objects'/rel).parent.glob(rel.stem+'.*'):
  shutil.copy2(artifact,(O/rel).parent/artifact.name)
assert (S/'baseline/TaskSupport.lean').read_bytes()==(N/'source/baseline/TaskSupport.lean').read_bytes()
assert 'TaskSupport' in base_ok
for artifact in (N/'objects').glob('TaskSupport.olean*'):shutil.copy2(artifact,O/artifact.name)
packages=json.loads((S/'baseline/formal-conjectures/lake-manifest.json').read_text())['packages'];deps=Path('/Users/jenwin/Documents/Codex/2026-10-07/p/work/current-official-baseline/formal-conjectures/.lake/packages')
profile='(version 1)\n(allow default)\n(deny network*)\n(deny file-write*)\n(deny file-read* (subpath "/Users"))\n(deny file-read* (subpath "/private/var/folders"))\n(deny file-read* (subpath "/private/tmp"))\n(allow file-read-metadata)\n'
for p in [R,TC,*[deps/p['name'] for p in packages]]:profile+=f'(allow file-read* (subpath {json.dumps(str(p.resolve()))}))\n'
profile+=f'(allow file-write* (subpath {json.dumps(str(R))}))\n(allow file-write* (literal "/dev/null"))\n';(R/'sandbox.sb').write_text(profile)
env={'PATH':str(TC/'bin')+':/usr/bin:/bin','HOME':str(R/'home'),'TMPDIR':str(R/'tmp'),'LANG':'en_US.UTF-8','LEAN_PATH':os.pathsep.join(map(str,[O,*[deps/p['name']/'.lake/build/lib/lean' for p in packages]])),'LEAN_NUM_THREADS':'1','LEAN_ABORT_ON_PANIC':'1'}
(R/'environment.json').write_text(json.dumps(env,indent=2)+'\n')
result={'status':'RUNNING','proof_commit':PIN,'started_utc':dt.datetime.now(dt.timezone.utc).isoformat(),'commands':[],'baseline':'189 baseline modules and TaskSupport freshly compiled in adjacent verification1057 run, source bytes matched exactly, copied objects only after successful command receipts','baseline_receipt_sha256':sha(R/'baseline-receipt-at-copy.json'),'source_hashes':{r['path']:r['sha256'] for rows in orders.values() for r in rows},'worker_count':3};save()
def command(label,args,export=False):
 log=R/'logs'/f'{label}.log';outpath=R/'Erdos1057-original.ndjson' if export else log;t=time.monotonic();argv=['/usr/bin/sandbox-exec','-f',str(R/'sandbox.sb'),*map(str,args)]
 print('START',label,flush=True)
 with outpath.open('wb') as out:
  with (R/'logs/export-stderr.log').open('wb') if export else open('/dev/null','wb') as err:
   p=subprocess.run(argv,cwd=S/'modular/src',env=env,stdout=out,stderr=err if export else subprocess.STDOUT)
 row={'label':label,'argv':argv,'cwd':str(S/'modular/src'),'exit_code':p.returncode,'seconds':round(time.monotonic()-t,3),'output':str(outpath.relative_to(R)),'sha256':sha(outpath),'bytes':outpath.stat().st_size}
 print('FINISH',label,p.returncode,row['seconds'],flush=True)
 return row
def checked(label,args,export=False):
 row=command(label,args,export);result['commands'].append(row);save();assert row['exit_code']==0,label;return row
try:
 rows=orders['modular'];names={r['module'] for r in rows};pending={r['module']:r for r in rows};done=set()
 with cf.ThreadPoolExecutor(max_workers=3) as pool:
  active={}
  while pending or active:
   for name,row in list(pending.items()):
    if len(active)>=3:break
    if set(row['dependencies'])&names<=done:
     rel=Path(name.replace('.','/')+'.olean');(O/rel).parent.mkdir(parents=True,exist_ok=True)
     future=pool.submit(command,'module-'+name,[TC/'bin/lean','--trust=0','-Dweak.google.answer=always_true','-DElab.async=false','-j1','-R',S/'modular/src','-o',O/rel,S/row['path']]);active[future]=name;del pending[name]
   assert active,'dependency cycle'
   finished,_=cf.wait(active,return_when=cf.FIRST_COMPLETED)
   for future in finished:
    name=active.pop(future);row=future.result();result['commands'].append(row);save();assert row['exit_code']==0,name;done.add(name)
 checked('audit-target',[TC/'bin/lean','--trust=0',S/'verification/AuditTarget.lean'])
 bridge=(N/'source/Independent1057.lean').read_text().replace('import Challenge','import ActualErdos1057Target').replace('checked1057','checked1057Original')
 (S/'Independent1057Original.lean').write_text(bridge)
 checked('independent-bridge',[TC/'bin/lean','--trust=0','--root='+str(S),'-o',O/'Independent1057Original.olean',S/'Independent1057Original.lean'])
 checked('kernel-replay',[TC/'bin/leanchecker','--verbose','ActualErdos1057Target'])
 checked('export-targets',[TC/'bin/leanexport','Independent1057Original','--','Bounty.target','checked1057Original'],True)
 config={'export_file_path':str(R/'Erdos1057-original.ndjson'),'permitted_axioms':['propext','Classical.choice','Quot.sound'],'unpermitted_axiom_hard_error':True,'unsafe_permit_all_axioms':False,'nat_extension':True,'string_extension':True,'pp_declars':['Intended1057','Bounty.target','checked1057Original'],'pp_to_stdout':True,'print_success_message':True,'pp_options':{'proofs':False,'width':120}}
 (R/'nanoda.json').write_text(json.dumps(config,indent=2)+'\n');checked('nanoda',[TC/'bin/nanoda_bin',R/'nanoda.json'])
 assert all(sha(S/path)==h for path,h in result['source_hashes'].items())
 result.update(status='SOURCE_BUILD_AXIOMS_KERNEL_AND_NANODA_PASSED',completed_utc=dt.datetime.now(dt.timezone.utc).isoformat(),source_unchanged=True)
except BaseException as e:result.update(status='FAILED',error=repr(e));raise
finally:save()
