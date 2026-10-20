#!/usr/bin/env python3
"""Portable source integrity and scope preflight; no Lean or network activity."""
from pathlib import Path
import hashlib,json,os,re,sys
R=Path(__file__).resolve().parents[1]
def module_header(raw):
    s=raw.decode('utf-8-sig')
    while True:
        s=s.lstrip()
        if s.startswith('--'):
            s=s.split('\n',1)[1]if '\n'in s else'';continue
        if s.startswith('/-'):
            depth=1;i=2
            while depth and i<len(s):
                if s.startswith('/-',i):depth+=1;i+=2
                elif s.startswith('-/',i):depth-=1;i+=2
                else:i+=1
            assert depth==0
            s=s[i:];continue
        return re.match(r'module\b',s)is not None
def sha(p):
    with p.open('rb')as f:return hashlib.file_digest(f,'sha256').hexdigest()
def main():
    frozen=json.loads((R/'audit/FROZEN_PROOF_SOURCE_MANIFEST.json').read_text())
    for row in frozen['files']:
        p=R/row['path'];assert p.is_file()and p.stat().st_size==row['bytes']and sha(p)==row['sha256'],row['path']
    manifest=json.loads((R/'lake-manifest.json').read_text())
    expected={p['name']:p['revision']for p in json.loads((R/'audit/FRESH_EVIDENCE_REUSE.json').read_text())['dependency_pins']}
    assert {p['name']:p['rev']for p in manifest['packages']}==expected
    assert (R/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0-rc2'
    config=json.loads((R/'comparator.json').read_text());assert config['challenge_module']=='Challenge'and config['solution_module']=='Solution'
    assert len(config['theorem_names'])==73 and config['definition_names']==[]
    challenge=(R/'Challenge.lean').read_text();solution=(R/'Solution.lean').read_text()
    for n in config['theorem_names']:
        name=n.removeprefix('LewkoDensityPalomar.');assert re.search(r'^theorem '+re.escape(name)+r'\b',challenge,re.M)and re.search(r'^theorem '+re.escape(name)+r'\b',solution,re.M)
    assert len(challenge.encode())<=100*1024 and len(challenge.splitlines())<=1000
    modules={};largest=0
    for base,dirs,files in os.walk(R):
        dirs[:]=[d for d in dirs if d not in ['.git','.lake']]
        for name in files:
            if not name.endswith('.lean'):continue
            p=Path(base)/name;assert not p.is_symlink();raw=p.read_bytes();lines=raw.count(b'\n')+(1 if raw and not raw.endswith(b'\n')else 0)
            assert module_header(raw)and lines<=10000,p
            largest=max(largest,lines);modules['.'.join(p.relative_to(R).with_suffix('').parts)]=p
    def imports(p):
        # Imported modules here are the frozen parser-audited source; this scan is
        # an additional source-level separation guard, not a replacement parser.
        return re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)',p.read_text(),re.M)
    assert all(n.startswith('Mathlib.')for n in imports(R/'Challenge.lean'))
    seen=set();todo=['Solution']
    while todo:
        m=todo.pop()
        if m in seen or m not in modules:continue
        seen.add(m);todo.extend(imports(modules[m]))
    assert 'Challenge'not in seen
    release_blockers=[]
    if not any((R/n).is_file()for n in ['LICENSE','LICENSE.md','LICENSE.txt']):release_blockers.append('Approved project license not yet activated at repository root')
    if not (R/'formalization.yaml').exists():release_blockers.append('Approved human metadata not yet activated as formalization.yaml')
    metadata_path=R/'formalization.yaml'
    if metadata_path.is_file():
        metadata=json.loads(metadata_path.read_text())
        assert metadata['project']['authors']==['Mark Lewko']
        assert metadata['project']['responsible_maintainers']==['Mark Lewko']
        assert metadata['project']['license']=='AGPL-3.0'
        assert metadata['project']['license_note']=='The machine identifier AGPL-3.0 uses the legacy SPDX spelling. The grant is GNU AGPL version 3 only (AGPL-3.0-only), as stated in LICENSING.md; upstream licenses and notices remain unchanged.'
        assert 'version 3 only (SPDX: AGPL-3.0-only)' in (R/'LICENSING.md').read_text()
        assert metadata['project']['description']==(R/'docs/presentation/PROPOSED_ABSTRACT.txt').read_text().strip()
    out=dict(status='PASS_SOURCE_INTEGRITY_AND_SCOPE',frozen_files=len(frozen['files']),regular_Lean_sources=len(modules),largest_Lean_physical_lines=largest,selected_theorems=73,fixed_definition_holes=0,Solution_local_import_modules=len(seen),Solution_imports_Challenge=False,compiler='4.35.0-rc2',dependency_pins=9,release_status='READY_FOR_REVIEW'if not release_blockers else'BLOCKED',release_blockers=release_blockers,hosted_Palomar_verification='NOT_RUN')
    print(json.dumps(out,indent=2))
    if '--require-release'in sys.argv and release_blockers:return 2
    return 0
if __name__=='__main__':raise SystemExit(main())
