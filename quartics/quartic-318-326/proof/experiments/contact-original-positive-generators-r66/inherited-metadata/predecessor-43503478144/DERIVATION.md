# Exact bounded proof repair

Normalize only the three named coordinate/transition aliases with simpa only when specializing the existing abstract coordinate_transport lemma. Its proof and all concrete maps remain unchanged. This removes goal-directed matching against opaque aliases; whether it resolves the reported specialization recursion requires hosted Lean.

## Required and constructed objects

The same arbitrary c : Fin 4 → ℚˣ, original line L, and infinity section m; no finite/reciprocal chart or scalar-extension carrier is replaced.

All coefficient indices of the finite and infinity ranks remain functions over their original Fin types; the changed proof introduces no truncation or reindexing.

finiteIso and infinityIso still map both original scalar extensions into the SAME common Laurent module. transition is exactly infinityIso ≪≫ finiteIso.symm. rawTransition is the same infinity-coordinate inverse, original transition, and finite-coordinate composite.

OriginalLaurentProjectiveOverlap318.Ring and ℚ-polynomial scalar extensions, with u↦T⁻¹ on the infinity chart, are unchanged.

The right side remains the actual reciprocal polynomial localization followed by rawTransition. The left side remains coordinates applied to the actual infinityRestriction. The rewrite of infinityRestriction_unit and the existing coordinates_unit equality hi are unchanged.

infinity_image and every downstream use of infinity_formula retain the same theorem statement and original Laurent transition.

All hypotheses and exceptional cases are unchanged. No independent acceptance or Lean success is claimed.
