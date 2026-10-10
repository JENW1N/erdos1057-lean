from pathlib import Path
import datetime as dt, hashlib, json, os, shutil, subprocess, time
RUN=Path(__file__).resolve().parent
REPO=RUN.parent/'proof1057'
TC=Path('/Users/jenwin/.elan/toolchains/leanprover--lean4---v4.35.0-rc2')
DEPS=Path('/Users/jenwin/Documents/Codex/2026-10-07/p/work/current-official-baseline/formal-conjectures/.lake/packages')
SOURCE=Path('/Users/jenwin/Documents/Codex/2026-10-07/p/outputs/Challenge.lean')
EXPECTED='20df80a9cba8503fe6cfceeccc6de2e7b7db94beb0532eed064ca1e2a65ff667'
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
assert sha(SOURCE)==EXPECTED
FROZEN=RUN/'source';OBJ=RUN/'objects';OBJ.mkdir(); FROZEN.mkdir()
orders=json.loads((REPO/'baseline/source-order.json').read_text())['modules']
for row in orders:
 src=REPO/row['path'];assert sha(src)==row['sha256']; dst=FROZEN/row['path'];dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
shutil.copyfile(REPO/'baseline/TaskSupport.lean',FROZEN/'baseline/TaskSupport.lean')
shutil.copyfile(SOURCE,FROZEN/'Challenge.lean')
packages=json.loads((REPO/'baseline/formal-conjectures/lake-manifest.json').read_text())['packages']
result={'started_utc':dt.datetime.now(dt.timezone.utc).isoformat(),'source_sha256':EXPECTED,'source_bytes':SOURCE.stat().st_size,'source_commit':'cfb1f033548a4fee78158958d369f5736a50ff73','compiler_sha256':sha(TC/'bin/lean'),'baseline_fresh':True,'custom_proof_fresh':True,'commands':[],'dependencies':[], 'status':'RUNNING'}
for p in packages:
 d=DEPS/p['name'];head=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip();assert head==p['rev'];assert not subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],text=True).strip()
 result['dependencies'].append({'name':p['name'],'commit':head,'tracked_source_clean':True,'artifacts':'existing local standard dependency cache'})
profile='(version 1)\n(allow default)\n(deny network*)\n(deny file-write*)\n(deny file-read* (subpath "/Users"))\n(deny file-read* (subpath "/private/var/folders"))\n(deny file-read* (subpath "/private/tmp"))\n(allow file-read-metadata)\n'
for p in [RUN,TC,*[DEPS/p['name'] for p in packages]]: profile+=f'(allow file-read* (subpath {json.dumps(str(p.resolve()))}))\n'
profile+=f'(allow file-write* (subpath {json.dumps(str(RUN))}))\n(allow file-write* (literal "/dev/null"))\n'
(RUN/'sandbox.sb').write_text(profile)
env={'PATH':str(TC/'bin')+':/usr/bin:/bin','HOME':str(RUN/'home'),'TMPDIR':str(RUN/'tmp'),'LANG':'en_US.UTF-8','LEAN_PATH':os.pathsep.join(map(str,[OBJ,*[DEPS/p['name']/'.lake/build/lib/lean' for p in packages]])),'LEAN_NUM_THREADS':'8','LEAN_ABORT_ON_PANIC':'1'}
save(RUN/'sandbox-environment.json',env)
# Check sandbox denials against a harmless control file outside the permitted run.
guard=RUN.parent/'sandbox-control.txt';guard.write_text('sandbox control\n')
probe='''import pathlib,socket,sys,json
p=pathlib.Path(sys.argv[1]);out={}
for name,op in [('outside_read',lambda:p.read_text()),('outside_write',lambda:p.write_text('changed')),('network',lambda:socket.create_connection(('127.0.0.1',9),timeout=1))]:
 try: op();out[name]='UNEXPECTED_ALLOWED'
 except PermissionError: out[name]='denied'
 except Exception as e: out[name]=type(e).__name__+': '+str(e)
print(json.dumps(out))
assert all(x=='denied' for x in out.values()),out
'''
flags=['--trust=0','-Dweak.google.answer=always_true','-DElab.async=true','-j8']
def command(label,args,cwd=FROZEN):
 start=time.monotonic();log=RUN/'logs'/f'{label}.log';argv=['/usr/bin/sandbox-exec','-f',str(RUN/'sandbox.sb'),*map(str,args)]
 print('START',label,flush=True)
 with log.open('wb') as out:r=subprocess.run(argv,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT)
 row={'label':label,'argv':argv,'exit_code':r.returncode,'seconds':round(time.monotonic()-start,3),'log':str(log.relative_to(RUN)),'log_sha256':sha(log)};result['commands'].append(row);save(RUN/'result.json',result)
 print('FINISH',label,r.returncode,row['seconds'],flush=True);assert r.returncode==0,f'{label}: see {log}'
 return log.read_text(errors='replace')
try:
 command('sandbox-self-test',['/usr/bin/python3','-c',probe,str(guard)])
 command('lean-version',[TC/'bin/lean','--version'])
 for i,row in enumerate(orders):
  dst=OBJ/(row['module'].replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
  command(f'baseline-{i:03d}',[TC/'bin/lean',*flags,'-R',FROZEN/'baseline/formal-conjectures','-o',dst,FROZEN/row['path']])
 command('TaskSupport',[TC/'bin/lean',*flags,'-R',FROZEN/'baseline','-o',OBJ/'TaskSupport.olean',FROZEN/'baseline/TaskSupport.lean'])
 command('Challenge',[TC/'bin/lean','--json',*flags,'--profile','-o',OBJ/'Challenge.olean',FROZEN/'Challenge.lean'])
 assert sha(FROZEN/'Challenge.lean')==EXPECTED
 result.update(status='SOURCE_COMPILED',completed_utc=dt.datetime.now(dt.timezone.utc).isoformat(),olean_sha256=sha(OBJ/'Challenge.olean'))
except BaseException as e:
 result.update(status='FAILED',error=str(e));raise
finally:save(RUN/'result.json',result)
