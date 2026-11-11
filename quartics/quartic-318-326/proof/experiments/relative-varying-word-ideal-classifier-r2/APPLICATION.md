# Application contract: Exact original word-ideal affine chart classifier

1. **source_requirements.** Required: The target ideals must have the specified word images as a basis, not merely be free.

Constructed: WordIdeal stores a basis b with b j=mk(w j) for every index.

Justification and boundary: The whole actual quotient ring is retained.

2. **constructed_objects.** Required: The chart classifier needs genuine inverse constructions.

Constructed: toWordIdeal transports the standard basis through the actual quotientEquiv; fromBasis uses the original ideal quotient multiplication action.

Justification and boundary: No abstract ring isomorphism class replaces the ideal.

3. **index_coverage.** Required: All chosen source words and every quotient vector must be covered.

Constructed: Every basis image equality is proved using quotientEquiv injectivity and the exact normalized evaluation.

Justification and boundary: Full cyclicity supplies the underlying quotient equivalence, not a rank comparison.

4. **transition_maps.** Required: The source-point and tensor-action descriptions must agree in both directions.

Constructed: toFrame/fromFrame use actual tensor adjunction inverses and prove both left/right inverses.

Justification and boundary: The recovered source action is not assumed to match the old one.

5. **hypothesis_checks.** Required: Normalized equations must imply actual word-basis equations.

Constructed: word_evaluation and fromFramed_action identify exactly1⊗word-products with the represented column identities.

Justification and boundary: No polynomial proxy or alternate coordinate word is substituted.

6. **consumer_identity.** Required: The final affine chart must classify original S⊗A ideals.

Constructed: classifier composes represented normalized ring points, actual normalized tensor frames, and exact word-basis ideals of S⊗A.

Justification and boundary: The supplied parameter ring and tensor source are unchanged.

7. **normalizations.** Required: Normalized representatives of an ideal must be unique.

Constructed: Injectivity applies the canonical equal-ideal intertwiner uniqueness at the same word basis.

Justification and boundary: Equality is on the full source action and marked vector, including nilpotents.

8. **downstream_boundary.** Required: A fixed-word all-ring equivalence is not already a global scheme classifier.

Constructed: Each fixed chart has its explicit two-sided ideal classification.

Justification and boundary: Naturality for coefficient ideal base change, regular overlap maps/cocycles, family gluing and global scheme classification remain open.

9. **evidence_acceptance.** Required: New applications and any proof-only cleanup require fresh review.

Constructed: All613 source files are pinned; existing quotient, basis, tensor and matrix APIs are retained. A separate bound note describes two direct map_one congrArg proof cleanups in CanonicalFrame.

Justification and boundary: Static checks do not establish Lean validity; independent review and hosted/kernel checks remain pending.



Two same-equality helpers in CyclicQuotientCanonicalFrame318.equiv_marked now use congrArg evaluation of map_one directly instead of rw[map_one];rfl. This avoids redundant tactic completion risk. No statement, hypothesis, map or later proof changes. No hosted failure was claimed for the former helpers. Exact609 other predecessor sources and all new modules are separately hashed.


## Explicit ideal dependency repair

Exact hosted234 isolated21-core failed at its first source: Ideal was not imported by Bilinear/Isomorphisms. Add public import Mathlib.RingTheory.Ideal.Basic before the actual ideal definition. This is the sole Lean change, all bodies and612 other sources exact. The error-recovery sorry warnings in that failed build were not source admissions and no artifact was accepted. Pinned IdealBasic source is already bound. Fresh review/hosted check required.
