# Finite five-contact metric and49/8 growth certificate

This packet proves32 finite/real inequalities in two Lean modules. It is genuine progress inside the geometric-height dependency, but is **not a proof of the entire five-contact height theorem**.

## Source locations and precise separation

- `manuscripts/quartic_v10.tex`, integral geometry/metric comparison around lines6930–7088: this is the geometric comparison(G), retained by the later exponent refinement.
- `quartics/quartic-318-326/docs/arithmetic.md`, lines1348–1446: the adopted49/8 exponent uses a different modular-Jacobian metric cancellation. It must not be identified with the older V10 exponent24 theorem or with the historical19/k detector wrapper.
- The downstream actual detector transfer for49/(8k) is in `detector-height-transfer`; it consumes three detector-height inequalities and does not manufacture them.

## Kernel-checked results

`FiveContactMetricBounds318` checks the six literal differences of0,32,76832,−343, their factorizations, exact lcm J=2765952000, and Cmet=12540153541944538512. It proves the integer comparison used in the additive metric budget. The vertical four-order inequality gives exactly the2delta loss; the negative-contact branch is also included.

The curvature algebra is checked, including the four-term reciprocal inequality and the gradient-square bound's contribution. Actual complex distances to all four literal contacts supply the radius separation, at-most-one-small-radius assertion, near-disc U bound, far-disc radius/U bounds, and the final uniform quotient

sum of triple radius products / (2U³) ≥ 1/Cmet.

This is an actual source-distance theorem, not an assumed list of radius bounds. Identifying that quotient with a lower bound for the smooth metric curvature, extending over branches/infinity, and applying the maximum principle remain geometric/analytic producers.

`Contact49Growth318` proves (1+1/p)^32≤p for every real p≥13, the exact exceptional product1152/385<3, and3·4608<2^14. It proves logR<12R^(1/32), hence4096+6logR<2^13R^(1/32), for R≥1. Finally it checks the exact implication

h≤2^11 d²L², d<2^14 C R^(97/32), L<2^13R^(1/32)

⇒ h<2^65 C²R^(49/8),

with C>0 and the relevant nonnegativity hypotheses. The input inequalities are explicit; no abstract whole-height theorem is introduced or discharged by this finite calculation.

## Fresh primary-source check

A fresh original copy of Javanpeykar, arXiv1403.6404v1, was retrieved from https://arxiv.org/pdf/1403.6404 and its relevant formulas visually inspected. The source hash is recorded in the receipt. Theorem2.4.1 and the definitions in§2.3 have exactly the Wronskian weight and averaged metric normalization used by cancellation. Lemma2.3.1 supplies a minimal-model inequality, not equality. Lemma2.4.4 records the GR normalization shift. Lemma4.2.3 requires p≤d; Theorem4.3.2 supplies that restriction for every vertical branch prime after choosing the semistable normalization. The decomposition in the proof of4.5.1 confirms the finite-intersection minus logarithmic-differential sign.

The direct-divisor extension argument has the correct sign: for Z=f*D−K, the negative exceptional part N would satisfy N.E≥Zplus.E≥0 on its support. Hence N²≥0, contradicting negative definiteness. This uses actual minimal-resolution adjunction and negative definiteness as geometric inputs; they have not been Lean-formalized here.

The local Wronskian argument also has the correct normalization: the source's orthonormal differential has area integral≤1 on the embedded disc; integrating its Taylor series gives the stated coefficient bound. The Wronskian definition includes the factorial denominators already. The same local coordinate must be used in both metric occurrences for exact cancellation.

## Open dependencies

This packet does not independently close:

1. The canonical Shimura/modular models, normalizer/fiber-field construction, and Yuan isometry with its metric normalization.
2. The actual modular vertical-support theorem p|6N and its compatibility with the semistable extension, plus the geometric divisor interpretation/negativity and projection formula.
3. The actual cusp disc and differential estimates, non-Weierstrass choice across all embeddings, Hilbert-space coefficient estimate/Hadamard application, and identification of the resulting height with the named arithmetic producer.
4. The actual level/index bounds feeding d and N, the image/isogeny/CM estimates, or final source witness decoding.

No mismatch was found in the freshly inspected Javanpeykar interfaces or finite constants. That is narrower than an end-to-end validation of the adopted49/8 theorem.

## Reproduction

Run `./build.sh`. All32 public theorems are kernel checked with `-Ddebug.skipKernelTC=false`; their axiom roots are only `propext`, `Classical.choice`, and `Quot.sound`. The complete audit and source hashes are in `receipt.json`. Repository files were not modified. Downloaded source PDF/text/screenshots are verification inputs, not necessary to vendor with the Lean checkpoint.
