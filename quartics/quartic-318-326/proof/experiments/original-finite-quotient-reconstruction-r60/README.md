# original-finite-quotient-reconstruction-r60

DRAFT SOURCE REPAIR; HOSTED LEAN PENDING. No independent acceptance or arithmetic theorem claim.

Revision of `original-finite-quotient-reconstruction-r59` at `56773da3e1a8045d885059ae17053fcbf0af6067`.

Replace impossible hidden-map instance registrations by explicitly scoped original coefficient actions and proofs, retaining the actual Cartesian integral-closure chart and its literal generic/base/point equations.

## Objects

Retain integral Y and projective B, the same dominant integral map p, normal domain A, open immersion j, coefficient homomorphism f and actual pullback square H. Order is the same integralClosure of Polynomial Q inside Y.functionField; no replacement ring, chart or generic point is chosen.

## Coefficient actions

quotientAlgebra p remains baseAlgebra p κ. Both FiniteDimensional and IsGalois binders are explicitly interpreted under that exact action. The native Polynomial Q action on the field is OriginalNormalClosureGalois318.baseAlgebra, the composite Polynomial Q→RatFunc Q→Y.functionField, definitionally the producer polynomialAlgebra p. The chart action is exactly ActualOpenFractionField318.sourceAlgebra j and A action is f.toAlgebra.

## Exact maps

The coefficient_tower and coefficient_integral proofs are obtained from the actual p,j,f,H producer at each use. IsFractionRing is obtained from the exact original open generic-stalk map j. sections is still OriginalNormalSectionClosure318.equivalence and specIso/ chart are the same Spec.mapIso followed by j.

## Native application and diagnosis

The hosted first errors reject global instance declarations whose hidden p,j,f cannot be inferred. Named data definitions and letI scopes remove that inference task. Three unchanged producer action definitions (polynomialAlgebra, chartAlgebra and coefficientAlgebra) are also exposed so their exact bodies can be compared across the module boundary; instance_reducible alone does not expose a def body in Lean 4.35.0. Integral-closure equivalence requires the same scalar tower, fraction ring, normality and integrality; all are supplied by the original constructed maps. The embedding theorem identifies the resulting integral-closure element with algebraMap A Y.functionField, which supplies fraction_chart. chart_base and point_coefficient use the same sections.commutes.

## Index and full-open coverage

All polynomials, full affine sections A and all ring maps Order(Y.functionField)→C remain quantified. No generic-only restriction, point subset, chart shrinking or replacement of the Cartesian square is introduced.

## Local hypotheses

Normality IsIntegrallyClosed A, domain/integral hypotheses, dominant integral p, open immersion j, actual IsPullback H and the finite-dimensional Galois structure under the original quotient action remain. No compatibility premise or arbitrary additional algebra action is assumed.

## Downstream consumers

OriginalCartesianCurveReconstruction318 invokes sections/chart/fraction_chart/chart_base/point_chart/point_coefficient with the existing p,j,f,H argument order and constructs the same quotient action, finite-dimensional and Galois structures from its original deck action. This consumer is retained byte-identical and must still pass hosted elaboration.

## Evidence and limitations

The exact hosted first failure, before source, result record and bounded patch are retained. Every other root Lean module is byte-identical to its published predecessor. No imports, heartbeat limits, admitted axioms, accepted baseline or artifact-cache policy change. Source inspection is not a Lean pass; fresh strict compilation, axiom audit and independent review remain pending. The complete concrete public targets and their actual downstream consumers must elaborate in hosted CI.

The pinned compiler source is Lean v4.35.0 src/Lean/Elab/MutualDef.lean: finishElab only auto-exposes abbrev/data-instance declarations or exposed sections, not ordinary instance_reducible defs. The three producer visibility changes preserve their bodies exactly.

The pinned primary integral-closure source is Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, `Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean`. Its native closure hypotheses are compared with the exact original Cartesian construction, not inferred from a verdict.
