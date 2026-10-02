# Independent mathematical review: final extension snapshot

Reviewed on 2026-10-02 by a separate Codex AI reviewing agent. This is a mathematical and source review, not human review or original-author endorsement. The reviewer did not edit proofs or run competing Lean builds.

**Result: pass. No unresolved mathematical or binder-to-prose defect found.**

Primary comparison source: [Bergemann–Morris, Theoretical Economics 11 (2016)](https://economics.mit.edu/sites/default/files/publications/paper_79_bce.pdf), Theorems 1 and 2 and their definitions and proofs.

## Exact scope

Theorem 1 concerns arbitrary finite players and states, heterogeneous finite action and signal spaces, arbitrary real utilities, actual nonnegative expansion kernels with original-signal marginals, and independent behavioral randomizations conditional on each player's own old and extra signals. The main theorem explicitly assumes normalized prior, information kernel and decision rule. BCE itself means weighted obedience. Zero prior and signal masses are permitted. Exact induction agrees with the paper's quotient on positive original fibers; null fibers impose no additional restrictions on decision-rule values. The reverse proof handles arbitrary finite extra signals and genuinely mixed strategies, rather than assuming a recommendation form.

Theorem 2 explicitly assumes nonempty finite states and valid information kernels. Its order ranges over all finite heterogeneous action families, arbitrary real utilities, and full-support normalized common priors. The arbitrary-universe action-reindexing theorem removes the apparent universe restriction in the definition. Signal probabilities may be zero; no uniform-positive signal support, product-channel assumption, or selected-game restriction occurs. Its orientation is correct: individual sufficiency of the first structure implies a subset of the second structure's BCE outcomes. Empty action profiles cannot support a valid decision rule under these assumptions; empty player sets cause no obstruction.

## Complete proof chain

The forward order proof constructs a normalized transferred decision rule, uses a point mass on null target fibers, preserves the exact state-conditioned outcome, and expresses each new obedience gain as a nonnegative channel-weighted sum of original gains.

The converse starts with a genuine finite quadratic-scoring game. Its actions comprise original types and two signed coordinate perturbations of each type's report. Arbitrary real reports are legitimate labels for finite game actions. The weighted proper-score identity proves truthful obedience, including null types where total division returns the zero vector without asserting a conditional probability distribution. All-game inclusion supplies the transferred BCE. Its exact truthful outcome proves both marginals of the constructed coupling; off-tag profiles have zero weighted joint mass, not necessarily zero conditional decision-rule mass on null fibers.

Both signed deviations bound the independence residual. The source proves R = d(r - Mp), then uses 0 <= d,M <= 1 to obtain |R| <= delta without division by any coupling mass. The actual coupling polytope is compact, residual bounds are closed polynomial constraints, and the directed intersection gives one exact zero-residual coupling. Channels are normalized as M/d on nonnull types. Null original rows vanish, so a normalized fallback channel is valid there. State probabilities are cancelled only under explicit full prior support. Thus the coupling and conditional independence conclusion are proved, not assumed.

## Specializations and examples

OnePlayer.lean derives the explicit finite receiver obedience inequality and expansion characterization. OnePlayerOrder.lean proves exact equivalence of individual sufficiency and state-independent stochastic garbling, then its all-decision-game order characterization. The lower-level garbling equivalence needs original-kernel validity only; the information-order specialization additionally assumes nonempty states and both valid kernels, exactly as stated.

Examples.lean establishes binary revelation implementation with an impossible original signal, rejects opposite-state recommendations, and proves correlated coordination outcomes have two diagonal masses of one half and zero off-diagonal mass. OrderExamples.lean proves revelation garbles to a null experiment with an impossible signal, rejects the reverse order, and constructs a correlated two-player signal coupling with normalized individual marginals whose joint mass differs from the product of those marginals. These examples are substantive and their descriptions match the statements.

## Contract and documentation fidelity

README.md and formalization.yaml accurately distinguish Theorem 1's allowance of prior-zero states from Theorem 2's all-game full-support priors. Their probability hypotheses, nonempty-state condition, heterogeneous spaces, independent behavioral play, arbitrary-universe evidence, order orientation, null-event handling, and finite scope agree with the binders. They do not claim welfare optimization, infinite-space results, novelty, human review, or author endorsement.

Challenge has twenty genuine definition bodies, all textually matching the corresponding library definitions after whitespace normalization. Its thirteen theorem signatures textually match Solution's signatures. Exactly thirteen deliberate reference proof placeholders occur in Challenge; no placeholder, custom axiom, unsafe directive, or native decision procedure was found in BCE/*.lean or Solution. Solution forwards to the distinct Implementation and OrderImplementation proof namespaces. Audit lists the five named ScoringGame instances, and ContractAudit checks all thirteen public theorem names and twenty definition names.

Compiler success, transitive axiom outputs, official Comparator acceptance, independent kernels, hosted Linux CI, and exact sanitized rendering are separate validation gates. This review does not assert their completion. Any later source change requires checking its effect against this snapshot.

## Inspected SHA-256 snapshot

```text
372b918cd873353662c6506996e3cfcd0389da1d3def532f8985552fa0b88a9b  BCE.lean
5cc0da2ce547271a8a87202aa8da4b8f642b6cbb495f4d4750b05246a3a4dc72  BCE/ActionReindex.lean
d7f232e28b3d29a01c2cc0e6efe93363948bf3b83f46829dcdce283fc05982df  BCE/Defs.lean
9849a99550cea3b45ef403092b1d3013e78ce0a6bd9cb20fae89972e94f7f84f  BCE/Examples.lean
6007b9f75b6194eba82de609650cdb2605ccdf901e2de2b5ea6b22f1acd172e8  BCE/Implementation.lean
ad0d0c9bb4283d2190ad6273ebcdbc3cf2fda9c74eaaa7a0e413050507213abb  BCE/InformationOrder.lean
24498595b342a0b6be1937b2dd30d0074ca5f725ce079bf15af191f4e9f0166e  BCE/OnePlayer.lean
ce73e77209638f5a31aedd0a54e77e916ca072fc50f9fc1a86a05a72ea850f82  BCE/OnePlayerOrder.lean
642f1fca0c8bf7be89c7d539edf19c95f6264b1f9e9d84fc70df882ab6f19c46  BCE/OrderCompactness.lean
1f352f5021752370882bbd4cf2b83b3c0f26f974bfdb901926584a9188f06f30  BCE/OrderDefs.lean
a24382052e4106ad441690e1ecf9be22c333e170c7e5fc5d43287b9835b64e81  BCE/OrderExamples.lean
838ab46162f7ac83e7a922db3e4238cb0df73caac90ecd0dc790873964034658  BCE/OrderMass.lean
6bd99fa34553639539fcdfd6cbbd3575caa67ce30810e08cba5f3d2c0baed7ac  BCE/OrderTransport.lean
137015cd24d2ce13e3b2ed0fd2d8aa2c3a1a18afdfa594f9c5f17317b3773f15  BCE/ScoringApproximation.lean
5c50ba9bec8353f4d6c07eb7e42091b3f4830ec904687a94fa11214ad24b7dc6  BCE/ScoringCore.lean
a624a3e9a9d0e94130e813572a7f973a9aa1fc9a0a04ab9e67b91921e62187ee  BCE/ScoringExtraction.lean
db1e70fc2e87789be596b56580dd326cc4b14449dce106553d3bff071197cd5c  BCE/ScoringGame.lean
7eb9c7323ff8d056a69c0c496ad6a7593165dd94b624ff60d216b5eed27761f5  BCE/Support.lean
9977c58e04fb2a94742c46591f6cfcf87c615e8a3699a625207353a6d909af25  Challenge.lean
43780a1da68e15a4f4fe520ba058fda37b326b31e4a3480f756db3130766c33a  Solution.lean
c01e0cf9f038847b26b0d6b2a87bbfd670eaf3e0efd92ec4b3b671adeb83e80c  Audit.lean
0754cd63470436cb6d1552eaa3d3d8bb8caff599cab9a8da6e7f4950682df356  ContractAudit.lean
18c122fc601ecbdd04a5c6d52d605b5dea69609d1c5ca1f787f6c59208dd1657  README.md
6e17e412453df22905a44fa9087c692a4719b3aa9bdeac8af3f1087ee938d4b7  formalization.yaml
```
