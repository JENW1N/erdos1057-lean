from pathlib import Path
import concurrent.futures as cf,datetime as dt,hashlib,json,os,subprocess,threading,time
RUN=Path(__file__).resolve().parent;FROZEN=RUN/'source';OBJ=RUN/'objects';TC=Path('/Users/jenwin/.elan/toolchains/leanprover--lean4---v4.35.0-rc2');REPO=RUN.parent/'proof1057';env=json.loads((RUN/'sandbox-environment.json').read_text());result=json.loads((RUN/'result.json').read_text());result['status']='RUNNING';result.pop('error',None);lock=threading.Lock()
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def save():(RUN/'result.json').write_text(json.dumps(result,indent=2)+'\n')
def command(label,args,cwd=FROZEN):
 log=RUN/'logs'/f'{label}.log';argv=['/usr/bin/sandbox-exec','-f',str(RUN/'sandbox.sb'),*map(str,args)];start=time.monotonic();print('START',label,flush=True)
 with log.open('wb') as stream:p=subprocess.run(argv,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
 row={'label':label,'argv':argv,'exit_code':p.returncode,'seconds':round(time.monotonic()-start,3),'log':str(log.relative_to(RUN)),'log_sha256':sha(log)}
 with lock:result['commands'].append(row);save()
 print('FINISH',label,p.returncode,row['seconds'],flush=True);assert p.returncode==0,str(log)
 return log.read_text(errors='replace')
orders=json.loads((REPO/'baseline/source-order.json').read_text())['modules'];index={r['module']:i for i,r in enumerate(orders)}
# Every completed module was built from frozen source during this fresh run.
done={orders[int(x['label'].split('-')[1])]['module'] for x in result['commands'] if x['label'].startswith('baseline-') and x['exit_code']==0}
result['commands']=[x for x in result['commands'] if x['exit_code']==0];result['baseline_scheduler']='three workers, one Lean thread each; completed fresh objects retained';save()
def build(row):
 dest=OBJ/(row['module'].replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists():dest.unlink()
 command(f"baseline-{index[row['module']]:03}",[TC/'bin/lean','--trust=0','-Dweak.google.answer=always_true','-DElab.async=false','-j1','-R',FROZEN/'baseline/formal-conjectures','-o',dest,FROZEN/row['path']]);return row['module']
try:
 pending={r['module']:r for r in orders if r['module'] not in done};running={}
 with cf.ThreadPoolExecutor(max_workers=3) as pool:
  while pending or running:
   for name,row in list(pending.items()):
    if len(running)>=3:break
    if set(row['dependencies']).intersection(index).issubset(done):running[pool.submit(build,row)]=name;del pending[name]
   assert running,'baseline dependency cycle'
   finished,_=cf.wait(running,return_when=cf.FIRST_COMPLETED)
   for f in finished:done.add(f.result());del running[f]
 flags=['--trust=0','-Dweak.google.answer=always_true','-DElab.async=true','-j8']
 command('TaskSupport',[TC/'bin/lean',*flags,'-R',FROZEN/'baseline','-o',OBJ/'TaskSupport.olean',FROZEN/'baseline/TaskSupport.lean'])
 command('Challenge',[TC/'bin/lean','--json',*flags,'--profile','-o',OBJ/'Challenge.olean',FROZEN/'Challenge.lean'])
 result.update(status='SOURCE_COMPILED',completed_utc=dt.datetime.now(dt.timezone.utc).isoformat(),olean_sha256=sha(OBJ/'Challenge.olean'));save()
except BaseException as exc:result.update(status='FAILED',error=str(exc));save();raise
