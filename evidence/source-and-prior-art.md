# Source and bounded prior-art inspection (2026-10-02)

Primary PDF: https://economics.mit.edu/sites/default/files/publications/paper_79_bce.pdf
Bergemann–Morris, Theoretical Economics 11 (2016), 487–522, DOI 10.3982/TE1808.
Source setup, Definitions 1–5, Theorem 1 and its forward/reverse proof were
inspected. Section 4/Theorem 2 was assessed separately and is not formalized.

Authenticated GitHub API code searches, one request each:

- `BayesCorrelated language:Lean`: total_count 0
- `Bergemann language:Lean`: total_count 0
- `"Bayes correlated" language:Lean`: total_count 0

The web interface could not access the registry API, but two bounded direct
HTTPS requests succeeded (HTTP 200) at the official endpoint. Queries `Bayes
correlated` and `Bergemann` returned empty entry arrays at revision 114 (405
results, 326 projects). Full bounded responses are in registry-search.json. No
absence or novelty conclusion is drawn from these searches.

Econlib has existing finite persuasion, Bayesian mixed-BNE and complete-information
correlated-equilibrium modules. Related Blackwell material exists in linglib.
Neither is treated as evidence that this theorem lacks prior formalizations.
The existing Crémér–McLean source was not changed. Recent Border and Rochet
packages were inspected for reusable validation and metadata workflows; this
mathematical proof has no dependency on them.

Current official policy/pipeline main revision, freshly verified through GitHub:
65f0154ed776cd26c224254aa57b379137f28b0d.
Minimum Lean v4.35.0-rc2; pinned Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.

Inspected related source snapshots:

- Econlib 003655ccf010cdf44c4f67d6675167b54ce0e9df, finite persuasion Basic.lean: signal structures and Bayes plausibility.
- linglib 2ec24ab91e78c9d9bb8afdabf24670ffc93aed44, Core/Probability/Decision/Blackwell.lean: garbling and Blackwell dominance.
