# Preventive unobserved cast-normalization repeat

Status: PREVENTIVE_UNOBSERVED_SOURCE_REVIEW_PENDING_HOSTED_NOT_REACHED. This module was not reached in run43568616769. It has no observed failure log of its own. The supporting observed error is the same matrix_trace_zero/cast-neg/change pattern in PELInertiaRealFixedPoints318, precisely bound in ../candidates/SOURCE-MANIFEST.json. One tactic line only is proposed; no local Lean or Lake has run.

1. Required source: matrix_trace_zero gives the actual real (1,1) entry = -A i. Coercion ℝ→ℂ is a ring hom and therefore preserves negation; push_cast normalizes that existing equality presentation.
2. Constructed input: all five original inertia elements, their literal split-real representation and original fixedPoint i. The target is the square of the exact complex Möbius denominator, not a different matrix or point.
3. Domain coverage: every i:Fin5, existing discriminant_real_positive and lower_left_positive proofs, all original assumptions unchanged. No nonzero or genericity premise is added.
4. Maps/directions: after rewriting real matrix_trace_zero, normalize ↑(-A i) to -(↑(A i)), then use the existing change to C*iPoint-A. No conjugation, inverse or sign reversal is introduced.
5. Result identity: original_denominator_square still proves denominator(matrix(inertiaElement i))(fixedPoint i)^2 = -(discriminant i:ℂ). It still uses the same denominator_value, Complex.I_sq and exact Real.sq_sqrt proof.
6. Direct consumer: original_derivative in the SAME module rewrites hdet and original_denominator_square in the quotient derivative, then proves the original numerator/negative denominator ratio = -1. This is the exact derivative at the same original point, not a related normalization or full stabilizer claim.
7. Scalars/signs: discriminant, square, minus sign, fixedPoint's positive imaginary part, and derivative -1 remain unchanged.
8. Public hypotheses/trust: only push_cast is inserted inside the existing proof. All theorem statements, assumptions, imports and option lines are byte-identical. No resource increase, admission, native evaluator or extra instance assumption.
9. Evidence/review: exact before/after hashes and patch are bound in MANIFEST.json; published predecessor is e3d4f334. Fresh internal source review must be authored separately from observed repairs and subsequent propagation must label this copy preventive/unobserved. No compiler result or mathematical acceptance is claimed.
