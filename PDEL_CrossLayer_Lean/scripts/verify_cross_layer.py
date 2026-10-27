#!/usr/bin/env python3
"""Real combined build/audit of the three original libraries and new bridges."""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
KIT = ROOT.parent
PIN = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}
BANNED = {'sorry','admit','axiom','native_decide','unsafe','run_elab',
          'implemented_by','csimp','elab','macro_rules','initialize','set_option',
          'declare_syntax_cat','syntax','opaque'}


def stripped(text: str) -> str:
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; out.extend('  '); i += 2
            elif text.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if text[i]=='\n' else ' '); i += 1
        elif quoted:
            if text[i]=='\\' and i+1<len(text): out.extend('  '); i += 2
            elif text[i]=='"': quoted=False; out.append(' '); i += 1
            else: out.append('\n' if text[i]=='\n' else ' '); i += 1
        elif text.startswith('/-',i): depth=1; out.extend('  '); i += 2
        elif text.startswith('--',i):
            end=text.find('\n',i)
            if end<0: end=len(text)
            out.extend(' '*(end-i));i=end
        elif text[i]=='"': quoted=True;out.append(' ');i+=1
        else:out.append(text[i]);i+=1
    if depth or quoted: raise ValueError('Unclosed Lean comment or string')
    return ''.join(out)


def inventory(path: Path) -> list[tuple[str,str]]:
    text=stripped(path.read_text());stack=[];names=[]
    for line in text.splitlines():
        line=line.strip()
        m=re.fullmatch(r'namespace\s+([\w.]+)',line)
        if m:stack.extend(m[1].split('.'));continue
        m=re.fullmatch(r'end\s+([\w.]+)',line)
        if m:
            parts=m[1].split('.')
            if stack[-len(parts):]!=parts:raise ValueError('Namespace mismatch: '+str(path))
            del stack[-len(parts):];continue
        m=re.match(r'(?:@\[[^\]]+\]\s*)*(theorem|lemma|def|abbrev)\s+(\w+)\b',line)
        if m:names.append((m[1],'.'.join(stack+[m[2]])))
        if re.search(r'\b(private|protected)\s+(theorem|lemma|def)\b',line):
            raise ValueError('Untracked private/protected declaration')
    if stack:raise ValueError('Unclosed namespace')
    return names


def check_lock(base: Path, lock: dict[str,str]) -> dict[str,str]:
    actual={}
    for name,expected in lock.items():
        p=base/name
        actual[name]=hashlib.sha256(p.read_bytes()).hexdigest()
        if actual[name]!=expected:raise ValueError('Original source changed: '+name)
    return actual


def parse_axioms(text: str, targets: list[str]) -> dict[str,list[str]]:
    found={}
    records=re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]",text,re.S)
    records += [(n,'') for n in re.findall(r"'([^']+)'\s+does not depend on any axioms",text)]
    for name,body in records:
        if name in found:raise ValueError('Duplicate audit record: '+name)
        found[name]=sorted({x.strip() for x in body.split(',') if x.strip()})
    if set(found)!=set(targets):raise ValueError('Missing or unexpected audit targets')
    if any(set(v)-ALLOWED for v in found.values()):raise ValueError('Disallowed axiom dependency')
    return found


def policy() -> dict:
    lock=json.loads((ROOT/'source_lock.json').read_text())['sha256']
    check_lock(KIT,lock)
    lean=ROOT/'lean';registry=json.loads((lean/'bridge_targets.json').read_text())
    all_old=[]
    for folder,manifest,namespace,driver in [
        (KIT/'lean','theorems.json','PdelMHD','CheckAxioms.lean'),
        (KIT/'PDEL_Layer2_Lean/lean','layer2_theorems.json','PdelBasic','CheckLayer2Axioms.lean'),
        (KIT/'PDEL_Layer3_Lean/lean','layer3_theorems.json','PdelEulerian','CheckLayer3Axioms.lean')]:
        expected=json.loads((folder/manifest).read_text())['targets']
        actual=[n for f in sorted((folder/namespace).glob('*.lean')) for k,n in inventory(f) if k in {'theorem','lemma'}]
        printed=re.findall(r'^#print axioms\s+(\S+)',(folder/driver).read_text(),re.M)
        if set(actual)!=set(expected) or set(printed)!=set(expected):raise ValueError('Original target mismatch')
        all_old+=expected
    new=[];theorems=[]
    for f in sorted((lean/'PdelBridge').glob('*.lean')):
        code=stripped(f.read_text())
        if '#' in code or set(re.findall(r'\b\w+\b',code)) & BANNED:
            raise ValueError('Disallowed proof command/token: '+f.name)
        for imp in re.findall(r'^import\s+(\S+)',code,re.M):
            if imp not in {'Mathlib','PdelMHD','PdelBasic','PdelEulerian'} and not imp.startswith(('PdelBridge.','PdelMHD.','PdelBasic.','PdelEulerian.')):
                raise ValueError('Unexpected proof import: '+imp)
        for kind,name in inventory(f):
            if not name.startswith('PdelBridge.'):raise ValueError('Wrong bridge namespace')
            new.append(name)
            if kind in {'theorem','lemma'}:theorems.append(name)
    if all_old!=registry['original_targets'] or new!=registry['bridge_targets'] or theorems!=registry['bridge_theorems']:
        raise ValueError('Source/registry mismatch')
    targets=all_old+new
    if targets!=registry['targets'] or len(targets)!=len(set(targets)):raise ValueError('Target omission/duplication')
    for name,prefix,expected in [('CheckAllAxioms.lean','#print axioms',targets),
                                 ('CheckBridgeStatements.lean','#check',theorems)]:
        expected_text='import PdelBridge\n'+''.join(prefix+' '+n+'\n' for n in expected)
        if re.sub(r'\s+',' ',stripped((lean/name).read_text())).strip()!=re.sub(r'\s+',' ',expected_text).strip():
            raise ValueError('Audit driver changed: '+name)
    imports=['PdelMHD','PdelBasic','PdelEulerian']+['PdelBridge.'+f.stem for f in sorted((lean/'PdelBridge').glob('*.lean'))]
    root_code=stripped((lean/'PdelBridge.lean').read_text())
    if set(re.findall(r'^import\s+(\S+)',root_code,re.M))!=set(imports) or re.sub(r'^import\s+\S+\s*$','',root_code,flags=re.M).strip():
        raise ValueError('Root imports do not cover all libraries/modules')
    config=tomllib.loads((lean/'lakefile.toml').read_text())
    if config['defaultTargets']!=['PdelBridge'] or [x['name'] for x in config['lean_lib']]!=['PdelBridge']:
        raise ValueError('Bridge build target changed')
    deps={x['name']:x for x in config['require']}
    if deps['mathlib']['rev']!=PIN:raise ValueError('mathlib pin changed')
    for dep,path in [('pdel_mhd',KIT/'lean'),('pdel_basic_variation',KIT/'PDEL_Layer2_Lean/lean'),('pdel_layer3',KIT/'PDEL_Layer3_Lean/lean')]:
        if (lean/deps[dep]['path']).resolve()!=path.resolve():raise ValueError('Local source dependency changed')
    if (lean/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.19.0':raise ValueError('Toolchain pin changed')
    return registry


def fingerprint() -> dict[str,str]:
    paths=list((ROOT/'lean/PdelBridge').glob('*.lean'))
    paths += [ROOT/'lean'/n for n in ['PdelBridge.lean','lakefile.toml','lake-manifest.json','lean-toolchain','bridge_targets.json','CheckAllAxioms.lean','CheckBridgeStatements.lean']]
    paths += [ROOT/'source_lock.json',Path(__file__)]
    lock=json.loads((ROOT/'source_lock.json').read_text())['sha256']
    paths += [KIT/n for n in lock]
    return {str(p.relative_to(KIT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))}


def main() -> int:
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source-only',action='store_true');args=ap.parse_args()
    out=ROOT/'results'/('run-'+dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+str(os.getpid()));out.mkdir()
    report={'status':'NOT_RUN','proof_status':'NOT_RUN','build_status':'NOT_RUN','axiom_status':'NOT_RUN','logs':[]}
    def run(cmd,name):
        print('>>>',' '.join(cmd),flush=True)
        p=subprocess.run(cmd,cwd=ROOT/'lean',capture_output=True,text=True,timeout=3600)
        s=p.stdout+p.stderr;(out/name).write_text(s);report['logs'].append(name)
        if p.returncode:raise RuntimeError(f'{cmd} exited {p.returncode}: {name}')
        return s
    rc=1
    try:
        registry=policy();report['target_counts']={**registry['original_counts'],'bridge_theorems':len(registry['bridge_theorems']),'bridge_declarations':len(registry['bridge_targets']),'all_audited':len(registry['targets'])}
        report['source_sha256']=fingerprint()
        if args.source_only:report['status']='SOURCE_ONLY';rc=0
        else:
            if not re.search(r'\bversion 4\.19\.0\b',run(['lake','env','lean','--version'],'01_version.log')):raise ValueError('Wrong Lean version')
            commit=run(['git','-C',str(ROOT/'lean/.lake/packages/mathlib'),'rev-parse','HEAD'],'02_mathlib.log').strip()
            if commit!=PIN:raise ValueError('Wrong mathlib commit')
            report['mathlib_commit']=commit;report['build_status']='RUNNING'
            build=run(['lake','build','PdelBridge'],'03_build.log');report['build_status']='PASS'
            if re.search(r'uses\s+[`\']?sorry|declaration uses',build):raise ValueError('Incomplete proof reported')
            run(['lake','env','lean','CheckBridgeStatements.lean'],'04_statements.log')
            report['axiom_status']='RUNNING'
            axioms=run(['lake','env','lean','CheckAllAxioms.lean'],'05_axioms.log')
            report['axioms']=parse_axioms(axioms,registry['targets']);report['axiom_status']='PASS'
            policy()
            if fingerprint()!=report['source_sha256']:raise ValueError('Sources changed during verification')
            report.update(status='PASS',proof_status='PASS',original_sources_unchanged=True,allowed_axioms=sorted(ALLOWED));rc=0
    except (ValueError,RuntimeError,OSError,subprocess.TimeoutExpired) as exc:
        for k in ['build_status','axiom_status']:
            if report[k]=='RUNNING':report[k]='FAIL'
        report.update(status='FAIL',proof_status='NOT_ACCEPTED',reason=str(exc))
    report['report_file']=str(out/'cross_layer.json')
    (out/'cross_layer.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in {'axioms','source_sha256'}},ensure_ascii=False,indent=2))
    return rc


if __name__=='__main__':raise SystemExit(main())
