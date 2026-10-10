from pathlib import Path
import datetime as dt, hashlib, json, subprocess, time
R=Path(__file__).resolve().parent
P=R.parent/'proof1057'
S=R/'source'; O=R/'objects'
TC=Path('/Users/jenwin/.elan/toolchains/leanprover--lean4---v4.35.0-rc2')
A='a95a41e18d13474150be7b127a4231e8c4c0e3af'
EXPECTED='20df80a9cba8503fe6cfceeccc6de2e7b7db94beb0532eed064ca1e2a65ff667'
env=json.loads((R/'sandbox-environment.json').read_text())
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def save(): (R/'final-result.json').write_text(json.dumps(result,indent=2)+'\n')
while True:
 source=json.loads((R/'result.json').read_text())
 if source['status']!='RUNNING':break
 time.sleep(2)
assert source['status']=='SOURCE_COMPILED',source['status']
assert sha(S/'Challenge.lean')==EXPECTED
assert subprocess.check_output(['git','show',A+':standalone/Challenge.lean'],cwd=P)==(S/'Challenge.lean').read_bytes()
(S/'Audit.lean').write_bytes(subprocess.check_output(['git','show',A+':standalone/Audit.lean'],cwd=P))
result={'status':'RUNNING','checked_proof_commit':A,'source_sha256':EXPECTED,'source_build_result':'result.json','started_utc':dt.datetime.now(dt.timezone.utc).isoformat(),'commands':[], 'tool_sha256':{n:sha(TC/'bin'/n) for n in ['lean','leanchecker','leanexport','nanoda_bin']}}
def command(label,args,export=False):
 log=R/'logs'/f'{label}.log'; t=time.monotonic();argv=['/usr/bin/sandbox-exec','-f',str(R/'sandbox.sb'),*map(str,args)];print('START',label,flush=True)
 with (R/'Erdos1057.ndjson' if export else log).open('wb') as out:
  with (R/'logs/export-stderr.log').open('wb') if export else open('/dev/null','wb') as err:
   p=subprocess.run(argv,cwd=S,env=env,stdout=out,stderr=err if export else subprocess.STDOUT)
 output=R/'Erdos1057.ndjson' if export else log
 row={'label':label,'argv':argv,'exit_code':p.returncode,'seconds':round(time.monotonic()-t,3),'output':str(output.relative_to(R)),'sha256':sha(output),'bytes':output.stat().st_size}
 result['commands'].append(row);save();print('FINISH',label,p.returncode,row['seconds'],flush=True);assert p.returncode==0,label
 return output
try:
 command('audit-fresh',[TC/'bin/lean','--trust=0',S/'Audit.lean'])
 command('independent-bridge',[TC/'bin/lean','--trust=0','-o',O/'Independent1057.olean',S/'Independent1057.lean'])
 command('kernel-replay',[TC/'bin/leanchecker','--verbose','Challenge'])
 command('export-targets',[TC/'bin/leanexport','Independent1057','--','Bounty.target','checked1057'],True)
 config={'export_file_path':str(R/'Erdos1057.ndjson'),'permitted_axioms':['propext','Classical.choice','Quot.sound'],'unpermitted_axiom_hard_error':True,'unsafe_permit_all_axioms':False,'nat_extension':True,'string_extension':True,'pp_declars':['Intended1057','Bounty.target','checked1057'],'pp_to_stdout':True,'print_success_message':True,'pp_options':{'proofs':False,'width':120}}
 (R/'nanoda.json').write_text(json.dumps(config,indent=2)+'\n')
 command('nanoda',[TC/'bin/nanoda_bin',R/'nanoda.json'])
 for name in ['audit-fresh','independent-bridge']:
  txt=(R/'logs'/f'{name}.log').read_text()
  assert 'sorryAx' not in txt and 'Lean.trustCompiler' not in txt
  assert "'Bounty.target' depends on axioms: [propext, Classical.choice, Quot.sound]" in txt,name
 assert sha(S/'Challenge.lean')==EXPECTED
 result.update(status='SOURCE_BUILD_AXIOMS_KERNEL_AND_NANODA_PASSED',completed_utc=dt.datetime.now(dt.timezone.utc).isoformat(),source_unchanged=True,export_sha256=sha(R/'Erdos1057.ndjson'),export_bytes=(R/'Erdos1057.ndjson').stat().st_size)
except BaseException as e:
 result.update(status='FAILED',error=repr(e));raise
finally:save()
