# Observed coercivity scalar positivity contract

Run 43597228569 at published 2af419e128047c483b3cdc0ba5e4d65c09d7c4ce. One proof-site candidate only; exact evidence and hashes in COERCIVITY-MANIFEST.json. No local Lean or accepted candidate result.

## 1. Required source input

The existing multiplication of hall by alpha*τ.im/20 needs that scalar nonnegative. Native mul_pos requires alpha_pos and the existing hτ:0<τ.im; div_pos additionally requires 0<20, discharged by norm_num; .le forgets strictness. These are exactly the old energy_lower inputs and the proved constant positivity in PELQuaternionRealRepresentation318. No new positivity theorem is assumed.

## 2. Constructed object

The actual Siegel matrix energy, coercive τ = alpha*τ.im/5*min 1 (1/Complex.normSq τ), hsum, hsmall and hall remain byte-identical. Only `by positivity` is replaced by explicit application of the native scalar lemmas. The actual τ, full real vector and all period normalization data remain unchanged.

## 3. Domain coverage

Every τ with the already explicit hτ:0<τ.im and every x:Fin 2→ℝ remain covered, including both signs and the zero vector. No rational approximation or additional nonzero hypothesis is introduced. The three public hτ telescope restorations from the preceding batch remain exactly unchanged; this batch adds no public binder or modifies any statement.

## 4. Maps and comparison direction

The same hall: m*4*(x0²+x1²)≤U+V/n is multiplied on the left by the same nonnegative alpha*τ.im/20. mul_le_mul_of_nonneg_left retains direction; the existing energy_squares rewrite and final arithmetic proof remain. No alternate energy or comparison map is used.

## 5. Scalars and local conditions

The denominator20 is positive in ℝ. alpha_pos is the proved positive real alpha from the actual quaternionic representation, not a free scalar. hτ is the actual parameter's imaginary part. Factors4,5,20, beta±1 and all square terms are untouched, as are normSq and the minimum. Explicit positivity proves a stronger strict inequality and then uses its nonnegative consequence.

## 6. Actual downstream consumers

PELOriginalThetaConvergence318.summability consumes coercive_positive τ hτ and energy_lower τ hτ for the entire integer-pair vector; PELOriginalScaledThetaConvergence318 uses the same quantities with its original positive scale. PELOriginalThetaSecondBounds318, PELOriginalThetaHolomorphy318 and PELOriginalScaledThetaHolomorphy318 retain the same positive coercivity constant. Their exact current source bytes are preserved alongside the actual SiegelMatrix/Normalization/QuaternionRealRepresentation definitions. No consumer premise is hidden or supplied by a surrogate object.

## 7. Exceptional cases

The original upper-half-plane premise implies τ≠0 through parameter_ne, already used in earlier lemmas. This candidate requires no new denominator condition. Zero vectors remain in the inequality; strict positivity is only of the constant scalar. Existing mathematical exceptional cases are unchanged.

## 8. Observed history

The authentic torsion-r23 artifact reports exactly one error at line43: failed positivity/nonnegativity/nonzeroness. The candidate replaces that proof presentation directly. Absence of other diagnostics within this failed module is not an independent theorem or module pass. The prior PELOriginalSiegelNormalization318 module genuinely passed in this run. Metadata, official ZIP digest, own RESULT/log and exact published intake/source hashes are retained.

## 9. Verification boundary

Only one proof-site expression changes; public telescopes, theorem targets, imports and resource/trust options remain identical. No sorry, axiom, placeholder, weakened bound or increased budget is introduced. Fresh independent source/application review is required, followed by exact-copy packet propagation with nine machine obligations. Candidate Lean/kernel/whole-packet acceptance remains unverified.
