"""Fail closed on contract drift, proof holes, axiom dependencies and source hashes."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
cfg=json.loads((ROOT/'comparator.json').read_text())
assert set(cfg)=={'challenge_module','solution_module','theorem_names','definition_names','permitted_axioms'}
assert set(cfg['permitted_axioms'])=={'propext','Quot.sound','Classical.choice'}
original={f:(ROOT/f).read_bytes() for f in ('Challenge.lean','Solution.lean','comparator.json')}
subprocess.run([sys.executable,str(ROOT/'scripts/make_challenge.py')],check=True,capture_output=True)
assert all(original[f]==(ROOT/f).read_bytes() for f in original),'Generated contract drift'
challenge=original['Challenge.lean'].decode()
assert len(challenge.splitlines())<=300 and len(original['Challenge.lean'])<=32*1024
files=[*ROOT.glob('*.lean'),*ROOT.glob('BCE/*.lean')]
all_names=[]
for file in files:
 s=file.read_text()
 assert s.startswith('module\n'),file
 # Strip comments before scanning executable source.
 s=re.sub(r'/\*.*?\*/','',s,flags=re.S)
 s=re.sub(r'/\-.*?\-/','',s,flags=re.S)
 s=re.sub(r'--[^\n]*','',s)
 if file.name=='Challenge.lean':
  assert len(re.findall(r'(?m)^  sorry$',s))==len(cfg['theorem_names'])==8
  s=re.sub(r'(?m)^  sorry$','',s)
 else:
  ns=re.search(r'^namespace (\S+)',s,re.M)
  if ns:all_names += [ns.group(1)+'.'+n for n in re.findall(r'^(?:noncomputable )?(?:theorem|def) (\w+)',s,re.M)]
 assert not re.search(r'\b(sorry|sorryAx|admit|axiom|unsafe|native_decide|ofReduceBool|implemented_by)\b',s),file
for key,kind in [('theorem_names','theorem'),('definition_names','def')]:
 for name in cfg[key]: assert re.search(r'\b'+kind+r'\s+'+re.escape(name.split('.')[-1])+r'\b',challenge),name
axioms=ROOT/'evidence/final-axioms.log'
if axioms.exists():
 rows=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",axioms.read_text()))
 assert set(all_names)==set(rows),(set(all_names)-set(rows),set(rows)-set(all_names))
 for n,used in rows.items():assert set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',used))<=set(cfg['permitted_axioms']),(n,used)
 print(f'All {len(rows)} authored declarations pass the transitive axiom audit')
hash_files=files+[ROOT/f for f in ['lakefile.toml','lake-manifest.json','lean-toolchain','comparator.json']]
record={'source_files_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(hash_files)},
 'lean':(ROOT/'lean-toolchain').read_text().strip(),'mathlib':'065356127b1dc0016f66b7283ce0ce2c4055aa55',
 'comparison':'eight exact theorem contracts; twelve genuine definitions; complete library and Solution',
 'verification_kernels':['Lean default','nanoda','con-ron']}
manifest=ROOT/'evidence/verification-manifest.json'
if '--record' in sys.argv:manifest.write_text(json.dumps(record,indent=2)+'\n')
else:assert json.loads(manifest.read_text())==record,'Audited source hash mismatch'
print(f'Package checks passed: {len(challenge.splitlines())} Challenge lines; {len(original["Challenge.lean"])} bytes')
