#!/usr/bin/env python3
"""Rebuild all construction proofs in a new directory against pinned Mathlib.

No shared source, Lake configuration, or previously generated local .olean is
used. Mathlib's compiled dependency cache must already be installed.
"""
from __future__ import annotations
import argparse,datetime,hashlib,json,os,re,shutil,subprocess,tempfile,time
from pathlib import Path

def output(cmd:list[str],cwd:Path)->str:
    return subprocess.check_output(cmd,cwd=cwd,text=True).strip()

def digest(p:Path)->str:
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main()->None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--formal-conjectures',type=Path,required=True)
    ap.add_argument('--lean',type=Path,required=True,help='Pinned Lean 4.33.1 binary')
    ap.add_argument('--output-parent',type=Path)
    args=ap.parse_args();root=Path(__file__).resolve().parent;fc=args.formal_conjectures.resolve();lean=args.lean.resolve()
    pins=json.loads((root/'DEPENDENCIES.json').read_text())
    assert output(['git','rev-parse','HEAD'],fc)==pins['formal_conjectures']['commit']
    assert (fc/'lean-toolchain').read_text().strip()==pins['lean_toolchain']
    mathlib=fc/'.lake/packages/mathlib'
    assert output(['git','rev-parse','HEAD'],mathlib)==pins['mathlib']['commit']
    basic=Path('FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean')
    assert digest(fc/basic)==pins['formal_conjectures']['ap_basic_sha256']
    version=output([str(lean),'--version'],fc)
    assert 'version 4.33.1,' in version,version
    for item in pins['modules']:
        assert digest(root/'formal'/(item['name']+'.lean'))==item['sha256'],item['name']
    parent=args.output_parent.resolve() if args.output_parent else None
    if parent:parent.mkdir(parents=True,exist_ok=True)
    build=Path(tempfile.mkdtemp(prefix='erdos142-construction-',dir=parent))
    (build/basic).parent.mkdir(parents=True)
    shutil.copy2(fc/basic,build/basic)
    for item in pins['modules']:
        shutil.copy2(root/'formal'/(item['name']+'.lean'),build/(item['name']+'.lean'))
    paths=[build,*sorted((fc/'.lake/packages').glob('*/.lake/build/lib/lean')),fc/'.lake/build/lib/lean',lean.parent.parent/'lib/lean']
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,paths))
    modules=[{'name':str(basic.with_suffix('')),'required_axiom_audits':[]}]+pins['modules']
    report={'status':'running','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lean_version':version,'pins':pins,'modules':[]}
    allowed={'propext','Classical.choice','Quot.sound'}
    for item in modules:
        name=item['name'];command=[str(lean),'-j1','-DwarningAsError=true','-o',name+'.olean',name+'.lean']
        started=time.monotonic()
        result=subprocess.run(command,cwd=build,env=env,text=True,capture_output=True,timeout=300)
        log=result.stdout+result.stderr
        (build/(name.replace('/','_')+'.log')).write_text(log)
        audits={n:[a.strip() for a in ax.split(',') if a.strip()] for n,ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)}
        for n in re.findall(r"'([^']+)' does not depend on any axioms",log):audits[n]=[]
        error=None
        if result.returncode:error='compiler failure'
        for required in item['required_axiom_audits']:
            if not any(n==required or n.endswith('.'+required) for n in audits):error='missing audit: '+required
        for n,axioms in audits.items():
            if not set(axioms)<=allowed:error='disallowed axioms: '+n+': '+repr(axioms)
        report['modules'].append({'module':name,'source_sha256':digest(build/(name+'.lean')),'exit_code':result.returncode,'seconds':round(time.monotonic()-started,3),'axiom_audits':audits,'error':error})
        report['status']='failed' if error else 'running'
        (build/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
        print(('FAIL' if error else 'PASS')+' '+name,flush=True)
        if error:
            print(log,flush=True);raise SystemExit(error)
    report['status']='passed';report['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    (build/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Fresh kernel replay passed: '+str(build/'verification.json'),flush=True)

if __name__=='__main__':main()
