# Bayes Correlated Equilibrium, Information Expansions and Information Order

A Lean 4 formalization of the finite information-expansion and information-order characterizations in
Bergemann and Morris, *Bayes correlated equilibrium and the comparison of
information structures in games* (Theoretical Economics 11, 2016), Theorems 1 and 2.

Authors and responsible maintainers: **Arthur Freitas Ramos**, **David Barros Hulak**,
and **Ruy Jose Guerra Barretto de Queiroz**.

For an arbitrary finite game and original information structure, a decision rule
is obedient if and only if a finite expansion supports a mixed Bayes–Nash
equilibrium inducing that rule. The proof constructs private action
recommendations and proves the converse for arbitrary finite extra signals and
independent behavioral randomizations. The formalization permits zero prior
masses, extending the paper's full-support prior assumption.

## Exact scope and assumptions

`I` is a finite player type, `Θ` a finite state type, and `A i` and `T i` are
player-specific finite action and original-signal types. Utilities are arbitrary
real functions of the entire action profile and state. No symmetry, conditional
independence of signals, common action space, or positivity of signal masses is
assumed. Probability hypotheses require nonnegative real masses summing to one.
These hypotheses enforce nonempty state and profile spaces wherever a probability
kernel exists; no separate support assumptions are hidden in the theorem.

| Lean binder or definition | Mathematical meaning |
| --- | --- |
| `ψ : Θ → ℝ`, `IsProbability ψ` | common prior |
| `π : Θ → (∀ i, T i) → ℝ`, `IsInformation π` | original signal kernel, normalized separately in every state |
| `u : I → (∀ i, A i) → Θ → ℝ` | heterogeneous players' utilities |
| `σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ`, `IsDecisionRule σ` | decision rule, normalized at every state and original signal profile |
| `BCE ψ π u σ` | weighted obedience inequalities for every player, own signal, recommended action, and unilateral deviation |
| `q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ`, `IsExpansion π q` | nonnegative joint kernel satisfying `∑ e, q θ t e = π θ t` in each state and original signal profile |
| `β : ∀ i, T i → E i → A i → ℝ`, `IsStrategy β` | behavioral action probabilities conditional only on the player's own old and extra signals |
| `MixedBNE ψ u q β` | every positively played action is a best response against opponents' independent randomizations |
| `Induces π σ q β` | `π θ t * σ θ t a = ∑ e, q θ t e * ∏ i, β i (t i) (e i) (a i)` |
| `Implementable ψ π u σ` | existence of finite extra-signal spaces, a marginal-preserving kernel, valid strategies, mixed BNE, and induction |

The public theorem `BayesCorrelated.finite_characterization` has all three
probability hypotheses and concludes `BCE ψ π u σ ↔ Implementable ψ π u σ`.
`BCE` itself denotes obedience, as in the paper; it does not bundle decision-rule
validity. The extra-signal existential uses the action universe `uA`; this imposes
no restriction on finite cardinalities. The reverse theorem is independently
polymorphic in the extra-signal universe `uE`.

The sum in `bestResponseGain` fixes the own action coordinate and uses a product
only over the other players. Thus it enumerates every opponent action profile
once. At null private signals, weighted expected payoffs are zero; the definitions
do not invent conditional beliefs there. `induces_iff_positive_support` proves
that exact joint-law induction agrees with the paper's quotient formula wherever
`π θ t > 0`. `expansion_null_fiber` proves every expansion mass on a null original
fiber is zero. Values of `σ` on those fibers remain arbitrary probability vectors.
`expansion_normalized` and `expansion_extra_information` establish that the joint
kernel and its extra-signal marginal are actual normalized information structures.
All expectations are finite sums, so no integrability assumption is needed.

## Proof and examples

The forward direction sets `E i = A i`, `q θ t a = π θ t * σ θ t a`, and has each
player follow their recommendation. The reverse direction factors the player's
own mixing probability from each expanded gain, uses the mixed best-response
inequality on positive action support, and sums over the player's extra signals.
There is no equilibrium-existence axiom or assumed characterization.

`BCE/OnePlayer.lean` derives the explicit single-receiver inequality
`∑ θ, ψ θ * π θ s * σ θ s x * (u x θ - u y θ) ≥ 0` and its expansion characterization.
`BCE/Examples.lean` proves binary state revelation is implementable, rejects a
recommendation to choose the opposite state, and proves a two-player coordination
rule has two diagonal outcomes of probability one half and no off-diagonal mass.
The binary example includes an original signal with probability zero.

## Information order: Theorem 2

`BayesCorrelated.information_order_characterization` proves, for valid finite
information kernels `π` and `ρ` on a **nonempty state space**,
`IndividuallySufficient π ρ ↔ MoreIncentiveConstrained π ρ`.
The direction is precise: a structure individually sufficient for another has a
subset of the other's BCE outcomes in every finite basic game.

| Lean binder or definition | Mathematical meaning |
| --- | --- |
| `IsCombination π ρ q` | a nonnegative joint signal kernel with **both** statewise marginals `π` and `ρ` |
| `HasIndividualChannels π q φ` | normalized channels `φ i s`, with `∑ e, (if e i = z then q θ t e else 0) = π θ t * φ i (t i) z` |
| `IndividuallySufficient π ρ` | existence of that coupling and those channels; cross-player channel correlation is allowed |
| `outcome π σ θ a` | the state-conditioned action kernel `∑ t, π θ t * σ θ t a` |
| `IsBCEOutcome ψ π u ν` | existence of a normalized obedient decision rule producing `ν` |
| `FullSupportPrior ψ` | a normalized common prior with `ψ θ > 0` in every state |
| `MoreIncentiveConstrained π ρ` | outcome inclusion for every finite heterogeneous action family, arbitrary real utilities and full-support prior |

The game quantifier's action universe contains the player, state and both signal
universes. `moreIncentiveConstrained_outcome_any_universe` proves that it applies to
action types in **any** Lean universe by finite-cardinality encoding and action
equivalences. There is no cardinality bound, selected-game restriction, product
garbling assumption, or positivity assumption on signal masses. Empty action
profiles cannot support normalized decision rules; their inclusion cases are
vacuous. Nonempty states are explicit because otherwise no normalized prior exists
and the all-game condition would be vacuous.

The forward proof transports a BCE through the common coupling and averages its
obedience gains with the individual channel weights. Null target fibers receive a
normalized point mass whose weighted joint contribution is zero.

The converse constructs genuine finite quadratic-scoring games. Player `i`'s
actions are `T i ⊕ (T i × (Θ × T₋ᵢ) × Bool)`: original reports and two signed
coordinate perturbations of each original belief. Report vectors are arbitrary
real vectors labeling finite actions. The weighted proper-scoring identity proves
truthful obedience even at null types, where total division gives the zero vector.
All-game inclusion supplies a transferred BCE; its exact truthful outcome yields
an actual coupling with both marginals. The signed deviations bound every
weighted independence residual by the positive perturbation size.

The coupling polytope is a closed subset of a finite compact cube. Directed closed
residual bounds give an exact zero-residual coupling. All limit equations are
weighted polynomial equations, defined at zero signal masses. Normalized channels
are recovered on positive type masses; null original rows vanish, allowing a
normalized fallback. State probabilities are cancelled only under the explicit
full-support assumption. Theorem 1's allowance of zero prior states does not alter
Theorem 2's all-basic-game prior assumption.

`BCE/OnePlayerOrder.lean` proves that individual sufficiency is exactly stochastic
garbling and derives its all-decision-game characterization. `BCE/OrderExamples.lean`
proves that revelation garbles to a null experiment with an impossible signal,
rejects the reverse order, and constructs correlated two-player channels that
satisfy individual sufficiency while their joint kernel differs from the product
of their marginals.

Infinite state, action, signal or player spaces, correlated private
randomization beyond the signal kernel, and welfare/persuasion optimization results
are outside this project's claim.

## Build and verification

Pinned Lean: `leanprover/lean4:v4.35.0-rc2`.
Pinned Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
lake update
lake exe cache get
lake build
lake env lean Audit.lean
```

`Challenge.lean` is a standalone statement contract importing only pinned Mathlib.
It has twenty genuine model definitions and thirteen exact theorem statements with
explicit reference proof placeholders. `Solution.lean` imports the complete
library and proves the same public statements using separate `Implementation` and
`OrderImplementation` namespaces. No proof placeholders occur in the library or Solution. Recreate the
contract with `python3 scripts/make_challenge.py`.

For full local verification, provide a checkout of the pinned official pipeline:

```sh
git clone https://github.com/PalomarRegistry/PalomarSubmission.git /tmp/bce-palomar-policy
git -C /tmp/bce-palomar-policy checkout 65f0154ed776cd26c224254aa57b379137f28b0d
# Install that pipeline's Python requirements in your preferred environment.
PALOMAR_SUBMISSION_DIR=/tmp/bce-palomar-policy ./scripts/verify.sh
```

`./scripts/verify.sh` validates the official metadata and Comparator configuration,
compiles Challenge and Solution separately, audits every authored declaration's
transitive axioms, checks Challenge's import closure, and runs the official bundled
Comparator with Lean's kernel, NanoDa and con-ron. On macOS the Comparator is run
without a sandbox; hosted Linux CI uses bubblewrap. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted in proved declarations.

The two GitHub workflows perform clean Linux proof verification and exact pinned
Palomar Verso rendering plus sanitization. Rendering checks every produced HTML
file against the 8 MiB limit. Evidence records source hashes and completed checks;
repository workflows perform validation only and never initiate Palomar intake or
registration. This repository is not a registered Palomar result.

## Source and credit

Primary source: [Bergemann–Morris paper](https://economics.mit.edu/sites/default/files/publications/paper_79_bce.pdf),
Section 2, Definitions 1–5 and Theorem 1, pages 493–496; Definition 6, Definition 7
and Theorem 2, pages 497 and 502–506. The second proof uses the paper's quadratic
scoring argument with a finite signed-coordinate test set and weighted compactness.
This is a source-based formalization and the complete proof development is in this
repository. Bounded GitHub Lean code searches for `BayesCorrelated`, `Bergemann`, and
`"Bayes correlated"` returned no matches on 2026-10-02; the official registry queries `Bayes correlated` and `Bergemann` also returned
empty entry arrays at revision 114. Those observations do not establish novelty or priority. Related
formalizations include [Econlib](https://github.com/danlyng/Econlib) (persuasion) and
[linglib](https://github.com/hawkrobe/linglib) (Blackwell comparison). The existing
Crémér–McLean development was not modified.

Codex assisted with source inspection, proof development, documentation, and
verification. Separate AI agents reviewed mathematics and final source fidelity.
No human mathematical review or original-author endorsement is claimed.
See `formalization.yaml`, `CITATION.cff`, and `evidence/` for metadata and validation.

License: BSD-3-Clause.
