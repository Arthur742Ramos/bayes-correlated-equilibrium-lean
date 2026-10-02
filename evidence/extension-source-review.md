# Independent source review: information-order extension

Review date: 2026-10-02. Reviewer: separate OpenAI Codex source-review agent.
This is an AI source and semantic review, not a human review or original-author endorsement.

## Outcome

PASS for the exact snapshots below. No substantive mathematical, statement-fidelity,
hidden-admission, circularity, or trust defect was found. No source-review blocker
remains. The theorem-2 result is an actual proved iff, not an assumed characterization.
The original theorem-1 proof source remains unchanged.

Primary reference: [Bergemann–Morris paper](https://economics.mit.edu/sites/default/files/publications/paper_79_bce.pdf),
Definitions 1–7, equations (8)–(9), and Theorems 1–2.

## Mathematical review

The information-order model preserves both statewise signal marginals and imposes
individual marginal channels rather than a product-channel restriction. Outcomes
require actual normalized obedient decision rules. The all-game order includes
arbitrary finite heterogeneous actions, real utilities, and full-support common
priors. Nonempty states are explicit; signal masses can vanish.

The forward transport preserves joint masses, outcomes, and weighted obedience.
Null target fibers receive an arbitrary normalized point mass whose weighted mass
is zero. The converse constructs genuine finite scoring games. Signed real report
vectors label finite actions and are valid under arbitrary utility functions. The
two signed coordinate deviations test every independence residual. Outcome equality
and nonnegativity yield an actual both-marginal coupling, including null target fibers.

Compactness is applied to a closed set of actual couplings in a finite cube and
continuous weighted equations. It produces one exact zero-residual coupling from
all positive approximation tolerances, without taking posterior ratios to a limit.
A uniform full-support prior supports the converse. State probabilities are cancelled
only under explicit positivity. Null original-type rows vanish and permit normalized
fallback channels. No result-assuming lemma is used along this chain.

Action reindexing covers finite action carriers in any Lean universe through lifted
cardinality sets. It preserves unilateral updates, probabilities, obedience, utilities,
and outcomes, then transfers the result back through inverse equivalences.
The one-player result is exactly state-independent stochastic garbling. Examples
verify revelation-to-null inclusion, failure of the reverse, and permissible correlated
two-player channels whose joint kernel differs from the product of marginals.

## Contract and package review

Independent read-only checks established:

- All 179 explicit authored definitions, theorems, and instances exactly match
  Audit.lean. Attribute-prefixed definitions and all five named scoring-game
  instances are covered; the earlier inventory omission is resolved.
- All 20 selected Challenge definitions have their exact library bodies. All 13
  library, Challenge, and Solution theorem headers agree byte for byte. Original
  variable and universe blocks are retained by the generator.
- ContractAudit checks all 33 comparator names. Definition names are genuine defs.
  Solution delegates to complete separately proved Implementation and
  OrderImplementation declarations. Challenge imports only Mathlib.
- No executable admission, custom axiom, unsafe proof, native_decide, or
  implemented_by occurs outside the 13 disclosed Challenge proof placeholders.
  The inventory rejects unnamed instances and nested comments. Automatically
  generated auxiliaries are checked transitively through the authored declarations.
- Package checks require exact declaration coverage in the axiom log, permitted
  transitive axiom sets, generated-contract fidelity, and exact source hashes.
  Both audit parsers recognize Lean's axiom-free output as an empty axiom set.
  The required allowed axioms are propext, Classical.choice, and Quot.sound.
- Comparator configuration permits only those standard axioms. Its two bundled
  external kernels are added to a temporary execution configuration outside the
  submitted tree, using the pinned official policy validator.
- README, formalization.yaml, citation, authors, maintainers, MSC2020 fields, and
  alignment names agree with the source. They distinguish theorem-1 zero-prior
  allowance from theorem-2 full-support priors, disclose finite scope, nonempty
  states, null-event treatment, and AI involvement. No unsupported novelty,
  human review, or original-author endorsement is claimed.
- Linux CI checks exact source hashes, compiles modules separately, audits all
  declarations, and requires all three kernel acceptance messages. Rendering uses
  the pinned official pipeline, requires sanitized pass status and exact source
  commit, and bounds every generated HTML file below 8 MiB. Neither workflow submits
  or registers a Palomar result.
- The opening Challenge title was corrected during review to name both theorems;
  hash reconstruction confirms this adjustment was title-only. The verify script's
  added trailing-whitespace normalization of evidence logs changes no validation
  condition or comparator acceptance requirement.

## Validation boundary

No proof or metadata file was edited and no competing Lean build was run.
At the parent's explicit request, the reviewer added defensive parsing of Lean's
axiom-free declaration lines to scripts/check_challenge_axioms.py, matching the
existing complete-library parser. Its reference-audit check was then run successfully:
13 selected theorem placeholders and 20 genuine definitions. This report was also
created by the reviewer. The parent reported successful
library, Challenge, and Solution builds. The completed final local evidence was inspected: the axiom log contains
exactly all 179 inventoried names, each using only permitted standard axioms; five
are explicitly axiom-free. The comparator log contains acceptance from con-ron,
NanoDa, and Lean default plus “Your solution is okay!”, with con-ron accepting
13,560 declarations. This is inspection of completed evidence, not a fresh
independent kernel replay by this reviewer. Exact sanitized rendering, hosted Linux
CI, publication, and the archive remain separate gates to report from their completed
evidence for the final immutable commit.

Review branch: `extension/information-order`. Base HEAD: `c6f0d94a36272dcd447ba82c017b5b7f98f0bad4`. The extension was uncommitted at review.

## Exact reviewed SHA256 snapshots

| File | SHA256 |
| --- | --- |
| `.github/workflows/render.yml` | `6165d3cf031d5190677aee0bea05ab94e398802d5ba82ca99f7e99d6dc014975` |
| `.github/workflows/verify.yml` | `1a69aa7331d87804f9d5b7a3ffc75fedc3a03236e3412c9bc532b0b82d0cdd3b` |
| `Audit.lean` | `c01e0cf9f038847b26b0d6b2a87bbfd670eaf3e0efd92ec4b3b671adeb83e80c` |
| `BCE.lean` | `372b918cd873353662c6506996e3cfcd0389da1d3def532f8985552fa0b88a9b` |
| `BCE/ActionReindex.lean` | `5cc0da2ce547271a8a87202aa8da4b8f642b6cbb495f4d4750b05246a3a4dc72` |
| `BCE/Defs.lean` | `d7f232e28b3d29a01c2cc0e6efe93363948bf3b83f46829dcdce283fc05982df` |
| `BCE/Examples.lean` | `9849a99550cea3b45ef403092b1d3013e78ce0a6bd9cb20fae89972e94f7f84f` |
| `BCE/Implementation.lean` | `6007b9f75b6194eba82de609650cdb2605ccdf901e2de2b5ea6b22f1acd172e8` |
| `BCE/InformationOrder.lean` | `ad0d0c9bb4283d2190ad6273ebcdbc3cf2fda9c74eaaa7a0e413050507213abb` |
| `BCE/OnePlayer.lean` | `24498595b342a0b6be1937b2dd30d0074ca5f725ce079bf15af191f4e9f0166e` |
| `BCE/OnePlayerOrder.lean` | `ce73e77209638f5a31aedd0a54e77e916ca072fc50f9fc1a86a05a72ea850f82` |
| `BCE/OrderCompactness.lean` | `642f1fca0c8bf7be89c7d539edf19c95f6264b1f9e9d84fc70df882ab6f19c46` |
| `BCE/OrderDefs.lean` | `1f352f5021752370882bbd4cf2b83b3c0f26f974bfdb901926584a9188f06f30` |
| `BCE/OrderExamples.lean` | `a24382052e4106ad441690e1ecf9be22c333e170c7e5fc5d43287b9835b64e81` |
| `BCE/OrderMass.lean` | `838ab46162f7ac83e7a922db3e4238cb0df73caac90ecd0dc790873964034658` |
| `BCE/OrderTransport.lean` | `6bd99fa34553639539fcdfd6cbbd3575caa67ce30810e08cba5f3d2c0baed7ac` |
| `BCE/ScoringApproximation.lean` | `137015cd24d2ce13e3b2ed0fd2d8aa2c3a1a18afdfa594f9c5f17317b3773f15` |
| `BCE/ScoringCore.lean` | `5c50ba9bec8353f4d6c07eb7e42091b3f4830ec904687a94fa11214ad24b7dc6` |
| `BCE/ScoringExtraction.lean` | `a624a3e9a9d0e94130e813572a7f973a9aa1fc9a0a04ab9e67b91921e62187ee` |
| `BCE/ScoringGame.lean` | `db1e70fc2e87789be596b56580dd326cc4b14449dce106553d3bff071197cd5c` |
| `BCE/Support.lean` | `7eb9c7323ff8d056a69c0c496ad6a7593165dd94b624ff60d216b5eed27761f5` |
| `CITATION.cff` | `ffe9d7078537dc7b4ae5b722e79761c335fa26e216c3b0967385728ee5af4399` |
| `Challenge.lean` | `9977c58e04fb2a94742c46591f6cfcf87c615e8a3699a625207353a6d909af25` |
| `ContractAudit.lean` | `0754cd63470436cb6d1552eaa3d3d8bb8caff599cab9a8da6e7f4950682df356` |
| `README.md` | `18c122fc601ecbdd04a5c6d52d605b5dea69609d1c5ca1f787f6c59208dd1657` |
| `Solution.lean` | `43780a1da68e15a4f4fe520ba058fda37b326b31e4a3480f756db3130766c33a` |
| `comparator.json` | `591f6cbe8a8b61c990bc6423da3c741be86a01d1ecd602e2f2fbc89774812fe1` |
| `formalization.yaml` | `6e17e412453df22905a44fa9087c692a4719b3aa9bdeac8af3f1087ee938d4b7` |
| `lake-manifest.json` | `53744843da49e0cee14dae12905c816c4de42ef557aad219408d73a270df23b9` |
| `lakefile.toml` | `e15e7e9521d5d9ede3ca600a645e9cbd13ab1fc11d156d86649b67136d4d868f` |
| `lean-toolchain` | `8dc8d6f560141069d9073e370611716ef77ada0da8ffa37e2149f44b2e63ac7a` |
| `scripts/authored_declarations.py` | `0095f7e556fc5dcb42a8d63e8b9a701face379faf6a777bd8840187e31cf1a82` |
| `scripts/check_challenge_axioms.py` | `c5d167c20975e31d607fc6d69bf450df05daee11a6f9e33e694162212473df7e` |
| `scripts/check_package.py` | `f215b06193e0aacb6e04f62aac497abcaccdca248ed85ea5f8e0c87444425996` |
| `scripts/make_challenge.py` | `4b4e4a621dd6abe14e830de961199a3084f518c21484346b0c2ee15e758458d4` |
| `scripts/verification_config.py` | `b84a028cbb89ed3f9b889126c352e5e2d2ae49b0f269f8aa1bf5ff6498157095` |
| `scripts/verify.sh` | `829df28203c0d3c8d617426af6beed5b4ada76da9e9a6aed2cdf3229964c0015` |
| `scripts/verify_metadata.py` | `07882873006462051a1a817703487bad0d5c5c79e7b4f42ca2f82abfc641ac3a` |
