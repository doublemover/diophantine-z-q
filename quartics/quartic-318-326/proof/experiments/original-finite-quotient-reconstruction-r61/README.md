# original-finite-quotient-reconstruction-r61

DRAFT SOURCE REPAIR; HOSTED LEAN PENDING. No independent application acceptance or full theorem claim.

Revision of `original-finite-quotient-reconstruction-r60` at `58753ec5f3b41268c5ceedae5264593b4f2aa0de`.

Scope the already constructed original coefficient algebra before projecting the exact sections isomorphism to the spectrum isomorphism.

## Objects

The same integral Y and projective B, dominant integral p, normal domain A, open immersion j, coefficient map f, Cartesian H and integral closure Order inside Y.functionField are unchanged.

## Coefficients

The added letI is coefficientAlgebra f, definitionally f.toAlgebra, exactly the A coefficient action already in sections. Quotient, finite-dimensional and Galois actions remain the original quotientAlgebra p. No arbitrary action or new scalar compatibility input is introduced.

## Exact maps

sections remains the same OriginalNormalSectionClosure318.equivalence built from coefficient_tower p j f H, coefficient_integral p j f H and ActualOpenFractionField318.fractionRing j. specIso still maps its same RingEquiv through Scheme.Spec; chart still composes its hom with j.

## Diagnosis and proof route

The first hosted error at63:27 is an unprintable instance-synthesis failure at the sections projection, followed by specIso/chart arity cascades. Adding the original coefficientAlgebra is a plausible bounded inference repair; the exact log does not identify the failed class, so this is not claimed as a conclusive diagnosis. Later point_coefficient has warnings only and receives no speculative edit. Exact source replay is required to establish whether this algebra-scope repair suffices. A pp.rawOnError option scoped only to specIso makes the next failure reveal the actual class; it changes error printing only, not elaboration, trust or resource behavior.

## Full coverage

All full affine sections, original chart points and polynomials retain the same quantifiers. No chart shrinking, replacement fraction map or generic-only substitute occurs.

## Local hypotheses

All existing normality/domain, dominant/integral map, open immersion, Cartesian square and original finite-dimensional Galois hypotheses remain. The new letI is derived data, not an additional premise.

## Downstream

OriginalCartesianCurveReconstruction318 remains byte-identical and uses the same p,j,f,H argument order, field action and original branch law. No theorem statement changes. The scoped raw-error printer is diagnostic only.

## Evidence and limits

Exact hosted failure, result, before source and bounded patch are retained. Every other root Lean file is byte-identical to the published predecessor. No imports/order, resource limits, admitted axioms, baseline or cache policy changes. Source review and structural checks are not Lean passes. Hosted strict compilation, recursive axiom audit and later-module checks remain pending.
