# Exact compact level-three j comparison on scheme points

Status: uncompiled inactive hosted-CI candidate. Distinct non-author source
review and strict Lean checking are pending. No local Lean build was run.

This packet combines the original compact complex-atlas/projective-point
comparison with the exact glued rational projective j morphism. Three new
modules supply numerator-localization evaluation, the action of the actual
scheme morphism on complex points, and its exact original-point and all-cusp
values on the original simultaneous compactification. A full-source exhaustion
argument proves uniqueness among maps having these same original/cusp values.

The pole values use the actual reciprocal target origin, not zero from a
totalized affine rational expression. The new action is actual composition of
scheme morphisms. No projective tuple, alternative parameter, dense-open
inference, or substitute compact source is introduced.

## Exact application contract

1. Exact original scheme and complex points. Required: The source and target must be the actual original rational projective scheme and base-preserving Spec C morphisms. Constructed: mapPoints composes each actual Points morphism with ThreeProjectiveJMap318.map; over_Q proves the result remains a Q-point. Application: The new action does not replace morphisms by tuples or choose a separate rational-coordinate function. It consumes the exact previously glued morphism, whose full Laurent overlap and rational structure identities remain in the closure.

2. Numerator localization factorization. Required: At a pole, a nonzero numerator must supply the reciprocal target chart without dividing by a zero denominator. Constructed: RationalPairNumeratorEvaluation318.evaluation_formula lifts any Q-algebra evaluation whose numerator image has a specified inverse through the actual numerator localization. Application: The proof identifies the lift on every base polynomial and on invSelf, then identifies the composed polynomial evaluation on coefficients and X. Applying the exact numerator_restriction yields an equality of scheme maps through original target chart 0.

3. Exact finite source formula. Required: The finite target formula needs explicit invertibility of the evaluated denominator, with the correct source restriction. Constructed: finite_formula assumes the actual denominator evaluation is nonzero, factors through its localization, and consumes ThreeProjectiveJMap318.finite_restriction. Application: The resulting coordinate is exactly the original rational polynomial quotient. No numerator nonvanishing is required, so numerator zeroes and elliptic points are retained.

4. Both actual source cusp origins. Required: Both source chart origins must map to actual target infinity as scheme points. Constructed: finite_zero uses finiteNumerator(0)=3^18 and finiteDenominator(0)=0; reciprocal_zero uses reciprocalNumerator(0)=1 and reciprocalDenominator(0)=0. Application: Both use the numerator localization theorem. They identify the target with chartPoint 0 0, never with the totalized finite expression at zero. Characteristic zero is explicit through C and Q, and the retained characteristic-three base point still excludes a false Z model.

5. Same compact analytic comparison. Required: The compact source must be the original simultaneous cusp filling, and its parameter comparison must retain the exact chart coordinates. Constructed: compactJ is mapPoints composed with ActualThreeProjectivePoints318.compactPointHomeomorph. Application: The imported compact point comparison has the original quotient parameter at every original point, reciprocal origin at infinityEnd, and finite origin at zeroEnd. The existing complex atlas and biholomorphism are retained unchanged rather than reconstructed with a different parameter.

6. Original modular j identity at all original points. Required: The target value must be the original QuotientJ318.jMap 3, including every exceptional original point. Constructed: original_value combines compactPointHomeomorph_original, original_finite_denominator_ne_zero, finite_formula and original_j_finite. Application: The parameter is the exact quotientParameter, already proved nonzero on the entire original quotient. The comparison is equality of actual scheme-valued points at every original b, not equality only on an admissible subset or equality of unrelated j expressions.

7. Complete cusp index coverage. Required: The comparison must cover every element of the actual End 3 index type, not merely two selected cusps. Constructed: infinity_value and zero_value use the exact point comparison at the named origins; cusp_value applies end_exhaustion to every actual end. Application: The existing theorem exhausts the same original end object used by the cusp filling. There is no substitution of abstract cusp labels or assumption that the selected names are exhaustive.

8. Global consumer and uniqueness. Required: A competing compact extension with the prescribed original and cusp values must be the exact scheme-induced map on the entire source. Constructed: unique_extension accepts both value laws on their full index types and proves F=compactJ. Application: original_or_cusp exhausts every filled source point. Each branch uses the exact corresponding original_value or cusp_value theorem, so equality needs neither a dense-open extension argument nor an unproved continuity assumption. This uniqueness theorem does not itself prove that an independently proposed extension satisfies the two value laws.

9. Unchanged sources, verification and remaining obligations. Required: Every changed application requires exact provenance, hosted checking and distinct review; no larger arithmetic conclusion follows automatically. Constructed: The packet contains the 44-source repaired point closure and seven additional unchanged projective-map sources plus three new modules, for 54 sources. Application: The shared first four sources are byte-identical. The r4 point heartbeat repair and r2 polynomial certificate repairs are inherited without further edits. Structural checks are not Lean validation. Continuity/holomorphy of the new induced j action, degree and ramification/finiteness, any integral model, universal-family/PEL identification and the full 318/326 theorem remain separate.

## Remaining verification and realization

The pointwise comparison does not yet assert continuity or holomorphy of the
new j action, a finite-map theorem, degree four or ramification indices. Those
properties of this exact morphism require their own proofs. The previously
built compact parameter comparison already carries its independent atlas
meaning, but is not a proof of these properties for an arbitrary scheme map.
Characteristic three still obstructs an everywhere-defined Z model from the
same polynomial pair. PEL/universal-family realization, arithmetic descent and
the full 318/326 theorem remain separate.

No prior submitted or failed-stage sources are changed. The complete inputs
are the repaired forward-projective-line-points-r4 and
forward-three-projective-j-map-r2 packets, with duplicate first-four sources
verified equal. Their pending hosted status is not upgraded here.
