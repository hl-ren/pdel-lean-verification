#!/usr/bin/env python3
"""Fresh build and per-declaration Lean audit; standard-library Python only."""
from pathlib import Path
import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}
PIN = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
TOOLCHAIN = 'leanprover/lean4:v4.19.0'

def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok, reason):
    if not ok: raise ValueError(reason)

def load_auditor(root):
    f = root / 'PDEL_CrossLayer_Lean/scripts/verify_cross_layer.py'
    spec = importlib.util.spec_from_file_location('pdel_bridge_auditor', f)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def inventory(code):
    stack, rows = [], []
    for line in code.splitlines():
        line = line.strip()
        m = re.fullmatch(r'namespace\s+([\w.]+)', line)
        if m:
            stack.extend(m[1].split('.')); continue
        m = re.fullmatch(r'end\s+([\w.]+)', line)
        if m:
            parts = m[1].split('.')
            require(stack[-len(parts):] == parts, 'Namespace mismatch')
            del stack[-len(parts):]; continue
        m = re.match(r'(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure|class)\s+(\w+)\b', line)
        if m: rows.append((m[1], '.'.join(stack + [m[2]])))
    require(not stack, 'Unclosed namespace')
    return rows

def check_sources():
    lock = read(ROOT/'verification/source_lock.json')
    for rel, digest in lock['sha256'].items():
        require(sha(ROOT/rel) == digest, 'Changed locked source/tool: '+rel)
    auditor = load_auditor(ROOT)
    auditor.policy()  # Original three-layer/bridge source and target gate.
    registry = read(ROOT/'verification/declarations.json')
    projects = read(ROOT/'verification/projects.json')
    expected = {r['name']: r for r in registry}
    require(len(expected) == len(registry) == 626, 'Declaration count/duplicates')
    actual, modules, package_checks = {}, {}, []
    git_lock = read(ROOT/'verification/dependencies.lock.json')
    pinned = {p['name']:p['rev'] for p in git_lock}
    for project in projects:
        lean = ROOT/project['path']; ns = project['namespace']
        config = tomllib.loads((lean/'lakefile.toml').read_text())
        manifest = read(lean/'lake-manifest.json')
        require(config['name'] == manifest['name'], 'Manifest root package mismatch')
        require((lean/'lean-toolchain').read_text().strip() == TOOLCHAIN, 'Toolchain changed')
        require({x['name']:x['rev'] for x in manifest['packages'] if x['type']=='git'} == pinned, 'Dependency lock mismatch')
        local = {x['name']:x for x in manifest['packages'] if x['type']=='path'}
        for dep in config['require']:
            if 'path' in dep:
                target = (lean/dep['path']).resolve()
                require(target.is_relative_to(ROOT), 'Local dependency escapes repository')
                require(tomllib.loads((target/'lakefile.toml').read_text())['name'] == dep['name'], 'Local package name mismatch')
                require((lean/local[dep['name']]['dir']).resolve()==target, 'Local manifest path mismatch')
            else:
                require(dep['name']=='mathlib' and dep['rev']==PIN, 'Unpinned external requirement')
        package_checks.append({'project':project['project'],'package':config['name'],'status':'PASS'})
        files = [lean/(ns+'.lean'), *sorted((lean/ns).glob('*.lean'))]
        for path in files:
            code = auditor.stripped(path.read_text())
            require(not (set(re.findall(r'\b\w+\b',code)) & auditor.BANNED) and '#' not in code, 'Forbidden proof command: '+str(path.relative_to(ROOT)))
            mod = '.'.join(path.relative_to(lean).with_suffix('').parts)
            modules[mod] = {'file':str(path.relative_to(ROOT)), 'project':project['project'],
                            'lean':project['path'], 'imports':re.findall(r'^import\s+(\S+)',code,re.M)}
            for kind, name in inventory(code):
                require(name not in actual, 'Duplicate declaration: '+name)
                actual[name] = (kind,str(path.relative_to(ROOT)),sha(path),mod,project['project'])
        names = [r for r in registry if r['project']==project['project']]
        require(len(names)==project['declarations'] and sum(r['kind'] in {'theorem','lemma'} for r in names)==project['theorems'], 'Project target count mismatch')
    require(set(actual)==set(expected), 'Missing or extra declarations')
    for name,(kind,file,digest,mod,project) in actual.items():
        row = expected[name]
        require((kind,file,digest,mod,project)==tuple(row[k] for k in ['kind','file','source_sha256','module','project']), 'Registry/source mismatch: '+name)
    visited, active = set(), set()
    def visit(n):
        require(n not in active, 'Cyclic source imports')
        if n in visited: return
        active.add(n)
        for imp in modules[n]['imports']:
            if imp.startswith('Pdel'):
                require(imp in modules, 'Unresolved local module: '+imp); visit(imp)
            else: require(imp=='Mathlib' or imp.startswith('Mathlib.'), 'Unexpected external source import: '+imp)
        active.remove(n); visited.add(n)
    for mod in modules: visit(mod)
    require(len(modules)==37, 'Module count changed')
    return lock, registry, projects, modules, auditor, package_checks

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only', action='store_true', help='Package/source checks only; Lean remains NOT_RUN.')
    parser.add_argument('--dependency-cache', type=Path, help='Optional directory containing the nine exact pinned Git dependencies; never project build outputs.')
    parser.add_argument('--work-dir', type=Path, help='New, non-existing output directory; default verification-runs/run-UTC-PID.')
    args = parser.parse_args()
    lock, registry, projects, modules, auditor, package_checks = check_sources()
    if args.check_only:
        print(json.dumps({'package_integrity':'PASS','source_policy':'PASS','declarations':len(registry),'modules':len(modules),'lean_build':'NOT_RUN','axiom_audit':'NOT_RUN'},indent=2)); return 0
    stamp = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    work = (args.work_dir or ROOT/'verification-runs'/('run-'+stamp+'-'+str(os.getpid()))).resolve()
    require(not work.exists(), 'Refusing to overwrite an existing run directory')
    require(not ROOT.is_relative_to(work), 'Output cannot contain the source repository')
    work.mkdir(parents=True); kit=work/'kit'; kit.mkdir(); out=work/'report';out.mkdir()
    deps = args.dependency_cache.resolve() if args.dependency_cache else work/'dependencies'
    env = os.environ.copy()
    for name in ['LEAN_PATH','LEAN_SRC_PATH','PDEL_RESULTS_DIR']: env.pop(name,None)
    env['PATH']=str(Path.home()/'.elan/bin')+os.pathsep+env['PATH']
    env['PYTHONDONTWRITEBYTECODE']='1'
    replacements=sorted([(str(work),'${RUN_DIR}'),(str(ROOT),'${REPO_DIR}'),(str(deps),'${DEPS_DIR}'),(str(Path.home()),'${HOME}')],key=lambda x:len(x[0]),reverse=True)
    def portable(value):
        if isinstance(value,str):
            for old,new in replacements: value=value.replace(old,new)
            return value
        if isinstance(value,list):return [portable(x) for x in value]
        if isinstance(value,dict):return {portable(k):portable(v) for k,v in value.items()}
        return value
    def write(name,value): (out/name).write_text(json.dumps(portable(value),indent=2,ensure_ascii=False)+'\n')
    state={'status':'NOT_RUN','utc':dt.datetime.now(dt.timezone.utc).isoformat(),'build':'NOT_RUN','axioms':'NOT_RUN','types':'NOT_RUN','dependencies':'NOT_RUN','commands':[],
           'not_run':['GitHub-hosted execution unless this is a GitHub run','full Maxwell','two-temperature PDEs','toroidal embedding','moving boundary','full homologous field/chart realization','physical validation'],
           'log_export':'Command output, with local path prefixes replaced by documented placeholders.'}
    def save():write('summary.json',state)
    def run(command,cwd,name,timeout=1800):
        print('RUN',name,flush=True);start=time.time();raw=out/(name+'.raw')
        with raw.open('w') as f:
            result=subprocess.run(command,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=timeout)
        text=raw.read_text();(out/name).write_text(portable(text));raw.unlink()
        state['commands'].append({'command':command,'cwd':str(cwd),'exit_code':result.returncode,'seconds':round(time.time()-start,3),'log':name});save()
        require(result.returncode==0, f'Command failed; see {name}')
        return text
    save()
    try:
        for rel in lock['copy_files']:
            target=kit/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/rel,target)
        for p in projects:
            lean=kit/p['path'];(lean/'.lake').mkdir();(lean/'.lake/packages').symlink_to(deps,target_is_directory=True)
            require(not (lean/'.lake/build').exists(), 'Project build cache copied')
        # Native mathlib cache helper uses Apple's current linker on macOS.
        if sys.platform=='darwin':
            env['LEAN_CC']=subprocess.check_output(['xcrun','--sdk','macosx','--find','clang'],text=True).strip()
            env['SDKROOT']=subprocess.check_output(['xcrun','--sdk','macosx','--show-sdk-path'],text=True).strip()
            prefix=subprocess.check_output(['lean','--print-prefix'],cwd=kit/'lean',env=env,text=True).strip()
            env['LIBRARY_PATH']=prefix+'/lib:'+prefix+'/lib/lean'+(':'+env['LIBRARY_PATH'] if env.get('LIBRARY_PATH') else '')
        version=run(['lean','--version'],kit/'lean','01_lean_version.log')
        require(re.search(r'\bversion 4\.19\.0\b',version), 'Wrong Lean version')
        if not args.dependency_cache:
            deps.mkdir()
            for i,dep in enumerate(read(ROOT/'verification/dependencies.lock.json')):
                target=deps/dep['name'];target.mkdir()
                run(['git','init','--quiet'],target,f'02_{i}_init.log')
                run(['git','remote','add','origin',dep['url']],target,f'02_{i}_remote.log')
                run(['git','fetch','--depth','1','origin',dep['rev']],target,f'02_{i}_fetch.log')
                run(['git','checkout','--detach','FETCH_HEAD'],target,f'02_{i}_checkout.log')
        def check_pins():
            checks=[]
            for dep in read(ROOT/'verification/dependencies.lock.json'):
                path=deps/dep['name']
                head=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
                dirty=subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no'],text=True)
                require(head==dep['rev'] and not dirty,'Wrong/dirty dependency: '+dep['name'])
                checks.append({'name':dep['name'],'rev':head,'tracked_worktree':'CLEAN'})
            return checks
        write('dependency_pins.json',check_pins())
        if not args.dependency_cache:
            run(['lake','exe','cache','get'],kit/'lean','03_mathlib_cache.log')
        state['dependency_setup']='VALIDATED_EXTERNAL_CACHE' if args.dependency_cache else 'FRESH_PINNED_FETCH';save()
        q=kit/'PDEL_Integration_Check/lean';state['build']='RUNNING';save()
        build=run(['lake','build','PdelIntegration'],q,'04_build.log')
        built=set(re.findall(r'\bBuilt (Pdel[\w.]+)',build))
        require(built==set(modules),'Missing fresh project build records: '+str(set(modules)-built))
        require(not re.search(r'uses\s+[`\']?sorry|declaration uses',build),'Incomplete proof in build output')
        state['build']='PASS';write('fresh_build.json',{'module_count':len(built),'modules':sorted(built),'project_outputs_reused':False});save()
        names=[r['name'] for r in registry]
        ax=out/'CheckAllAxioms.lean';ax.write_text('import PdelIntegration\n'+''.join('#print axioms '+n+'\n' for n in names))
        state['axioms']='RUNNING';save()
        axes=auditor.parse_axioms(run(['lake','env','lean',str(ax)],q,'05_axioms.log'),names)
        require(axes==read(ROOT/'verification/expected_axioms.json'),'Axiom dependencies differ from recorded baseline')
        state['axioms']='PASS';write('declarations.json',[r|{'status':'PASS','axioms':axes[r['name']]} for r in registry]);save()
        types=out/'CheckAllTypes.lean';types.write_text('import PdelIntegration\nset_option pp.all true\nset_option maxRecDepth 4096\nset_option pp.maxSteps 10000000\n'+''.join('#check '+n+'\n' for n in names))
        t=run(['lake','env','lean',str(types)],q,'06_full_types.log')
        require(all(n in t for n in names) and '⋯' not in t,'Missing/truncated full types');state['types']='PASS';save()
        driver=out/'CheckDependencies.lean';shutil.copy2(ROOT/'verification/CheckDependencies.lean',driver)
        t=run(['lake','env','lean',str(driver)],q,'07_dependencies.log')
        records=[json.loads(x) for x in re.findall(r'^PDEL_DEP (.*)$',t,re.M)];D={x['name']:x for x in records}
        loaded=[json.loads(x) for x in re.findall(r'^PDEL_MODULE (.*)$',t,re.M)]
        require(len(D)==len(records) and set(names)<=set(D),'Missing dependency records')
        require(all(x['unsafe'] and x['name'] not in names for x in records if x['kind']=='axiom'),'Custom safe result axiom')
        for n in names:
            seen=set();todo=[n]
            while todo:
                x=todo.pop()
                if x not in D or x in seen:continue
                seen.add(x);require(not D[x]['unsafe'],'Unsafe dependency of '+n)
                todo.extend(D[x]['type_dependencies']+D[x]['value_dependencies'])
        for check in read(ROOT/'verification/required_dependencies.json'):
            require(set(check['required_proof_dependencies'])<=set(D[check['declaration']]['value_dependencies']),'Required proof call missing: '+check['declaration'])
        require(set(x['module'] for x in loaded)==set(modules),'Unexpected loaded project modules')
        for x in loaded:
            m=modules[x['module']];expected=kit/m['lean']/'.lake/build/lib/lean'/Path(*x['module'].split('.')).with_suffix('.olean')
            actual=(q/x['olean']).resolve();require(actual==expected.resolve(),'Old/external project module loaded')
            x.update(resolved_olean=str(actual),sha256=sha(actual),status='PASS')
        write('proof_dependencies.json',records);write('module_resolution.json',loaded)
        write('import_graph.json',modules);write('package_dependencies.json',package_checks)
        state['dependencies']='PASS';save()
        for rel,digest in lock['sha256'].items():require(sha(ROOT/rel)==digest,'Repository changed during run: '+rel)
        for rel in lock['copy_files']:require(sha(kit/rel)==sha(ROOT/rel),'Isolated source/config changed: '+rel)
        check_pins();write('source_sha256.json',lock['sha256'])
        state.update(status='PASS',existing_theorems=407,existing_named_declarations=621,additional_interface_checks=5,total_audited_declarations=626,
                     fresh_modules=37,source_unchanged=True,allowed_axioms=sorted(ALLOWED),proof_dependency_records=len(records),projects=projects)
        state['not_run'][0]='GitHub-hosted execution: '+('THIS_RUN' if env.get('GITHUB_ACTIONS')=='true' else 'NOT_RUN')
        save();print('PASS: 37 freshly built modules, 626 audited declarations. Report: '+str(out/'summary.json'),flush=True);return 0
    except Exception as exc:
        state.update(status='FAIL',reason=str(exc));save();print('FAIL: '+str(exc),file=sys.stderr);return 1

if __name__=='__main__':
    sys.dont_write_bytecode=True
    try: raise SystemExit(main())
    except (OSError,ValueError,KeyError) as exc: print('PACKAGE CHECK FAILED: '+str(exc),file=sys.stderr);raise SystemExit(1)
