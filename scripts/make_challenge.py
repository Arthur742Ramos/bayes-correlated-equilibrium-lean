"""Generate the exact standalone statement contract and proved public Solution wrappers."""
from pathlib import Path
import json, re
ROOT=Path(__file__).resolve().parent.parent
specs=[
 ('Implementation','finite_characterization','ψ π u σ _hψ hπ hσ'),
 ('Implementation','mixedBNE_induces_BCE','ψ π u σ q β hβ hB hi'),
 ('Support','expansion_normalized','π q hπ hq θ'),
 ('Support','expansion_null_fiber','π q hq θ t h e'),
 ('Support','strategyProduct_isProbability','β hβ t e'),
 ('Support','induces_iff_positive_support','π σ q β hπ hq'),
 ('OnePlayer','onePlayer_obedienceGain','ψ π u σ s x y'),
 ('OnePlayer','onePlayer_characterization','ψ π u σ hψ hπ hσ')]
def header(file,name):
 s=(ROOT/f'BCE/{file}.lean').read_text()
 begin=s.index('theorem '+name+' ')
 end=s.index(' := by',begin)
 return s[begin:end]
def variables(file):
 s=(ROOT/f'BCE/{file}.lean').read_text()
 begin=s.index('universe ' if file!='OnePlayer' else 'variable ')
 end=s.index('\n\n',begin)
 # Implementation and Support have one contiguous variable block.
 return s[begin:end]
defs=(ROOT/'BCE/Defs.lean').read_text()
challenge=defs[:defs.rindex('end BayesCorrelated')]
challenge=challenge.replace('@[expose] public section\nopen scoped BigOperators','''/-! Finite Bergemann–Morris Theorem 1. All twelve model definitions have their
exact implementation bodies. Only the eight selected theorem proofs are deliberate
reference placeholders. Solution imports the complete proved library. Null signals
use weighted inequalities; zero-prior states are permitted. Theorem 2 is not claimed. -/
@[expose] public section
open scoped BigOperators''',1)
solution='module\npublic import BCE\n\n@[expose] public section\nopen scoped BigOperators\nnamespace BayesCorrelated\n'
# Remove initial variables from generated theorem sections by closing the namespace,
# and reopen with the original per-file variables for identical binder/universe names.
challenge+='end BayesCorrelated\n'
for file in ('Implementation','Support','OnePlayer'):
 block='namespace BayesCorrelated\n'+variables(file)+'\n\n'
 challenge+=block
 solution+=('end BayesCorrelated\n' if file=='Implementation' else '')+block
 for sf,name,args in specs:
  if sf!=file:continue
  h=header(file,name)
  challenge+=h+' := by\n  sorry\n\n'
  solution+=h+' := by\n  exact Implementation.'+name+' '+args+'\n\n'
 challenge+='end BayesCorrelated\n'
 solution+='end BayesCorrelated\n'
(ROOT/'Challenge.lean').write_text(challenge)
(ROOT/'Solution.lean').write_text(solution)
defnames=re.findall(r'(?:noncomputable )?def (\w+)',defs)
config={'challenge_module':'Challenge','solution_module':'Solution',
 'theorem_names':['BayesCorrelated.'+n for _,n,_ in specs],
 'definition_names':['BayesCorrelated.'+n for n in defnames],
 'permitted_axioms':['propext','Quot.sound','Classical.choice']}
(ROOT/'comparator.json').write_text(json.dumps(config,indent=2)+'\n')
print(f'{len(specs)} theorem contracts; {len(defnames)} genuine definitions')
