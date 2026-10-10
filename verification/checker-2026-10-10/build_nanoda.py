from pathlib import Path
import hashlib,json,os,subprocess,time
R=Path(__file__).resolve().parent;P=R/'nanoda';C=Path((R/'cargo-path.txt').read_text().strip());TC=C.parent.parent
for name in ['logs','home','cargo','tmp','target','clang-cache']:(R/name).mkdir(exist_ok=True)
for p in P.rglob('AGENTS.md'):print(p, p.read_text())
env={'PATH':str(TC/'bin')+':/usr/bin:/bin','HOME':str(R/'home'),'TMPDIR':str(R/'tmp'),'LANG':'en_US.UTF-8','CARGO_HOME':str(R/'cargo'),'CARGO_TARGET_DIR':str(R/'target'),'CARGO_BUILD_JOBS':'2','CLANG_MODULE_CACHE_PATH':str(R/'clang-cache')}
result={'repository':'https://github.com/ammkrn/nanoda_lib','commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'commands':[],'version':'0.4.19'}
profile='(version 1)\n(allow default)\n(deny network*)\n(deny file-write*)\n(deny file-read* (subpath "/Users"))\n(deny file-read* (subpath "/private/var/folders"))\n(deny file-read* (subpath "/private/tmp"))\n(allow file-read-metadata)\n'
for p in [R,TC]:profile+=f'(allow file-read* (subpath {json.dumps(str(p))}))\n'
profile+=f'(allow file-write* (subpath {json.dumps(str(R))}))\n(allow file-write* (literal "/dev/null"))\n';(R/'sandbox.sb').write_text(profile)
for label,args in [('fetch',[C,'fetch','--locked']),('build',['/usr/bin/sandbox-exec','-f',R/'sandbox.sb',C,'build','--release','--locked','--offline'])]:
 print('START',label,flush=True);t=time.monotonic()
 with (R/'logs'/f'{label}.log').open('wb') as out:p=subprocess.run(list(map(str,args)),cwd=P,env=env,stdout=out,stderr=subprocess.STDOUT)
 result['commands'].append({'label':label,'argv':list(map(str,args)),'exit_code':p.returncode,'seconds':round(time.monotonic()-t,3)});(R/'result.json').write_text(json.dumps(result,indent=2)+'\n');print('FINISH',label,p.returncode,flush=True);assert p.returncode==0,label
binary=R/'target/release/nanoda_bin';result['binary_sha256']=hashlib.sha256(binary.read_bytes()).hexdigest();result['status']='SOURCE_BUILD_PASSED';(R/'result.json').write_text(json.dumps(result,indent=2)+'\n')
