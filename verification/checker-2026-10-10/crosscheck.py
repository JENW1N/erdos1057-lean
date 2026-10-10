from pathlib import Path
import datetime,hashlib,json,subprocess,sys,time
T=Path(__file__).resolve().parent;R=Path(sys.argv[1]).resolve();B=T/'target/release/nanoda_bin';assert json.loads((T/'result.json').read_text())['status']=='SOURCE_BUILD_PASSED'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
efile=R/'environment.json'
if not efile.exists():efile=R/'sandbox-environment.json'
env=json.loads(efile.read_text());profile=R/'sandbox.sb';s=profile.read_text();rule=f'(allow file-read* (literal {json.dumps(str(B))}))\n'
if rule not in s:profile.write_text(s+rule)
log=R/'logs/nanoda-0.4.19.log';argv=['/usr/bin/sandbox-exec','-f',str(profile),str(B),str(R/'nanoda.json')];t=time.monotonic()
with log.open('wb') as out:p=subprocess.run(argv,cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
result={'checker':'nanoda_lib 0.4.19','repository':'https://github.com/ammkrn/nanoda_lib','source_commit':'3a2407216ee84a75f9e1aead6803d0578be06ae7','binary_sha256':sha(B),'cargo_lock_sha256':sha(T/'nanoda/Cargo.lock'),'argv':argv,'cwd':str(R),'exit_code':p.returncode,'seconds':round(time.monotonic()-t,3),'log':'logs/nanoda-0.4.19.log','log_sha256':sha(log),'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(R/'nanoda-latest-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));assert p.returncode==0
