# All-place local physical-anchor representations

Status: pending hosted Lean check and distinct bounded source review. No local Lean compilation/build. The general quadratic-form local-global theorem is an explicit remaining input, not an introduced axiom or a claimed proof of Hasse–Minkowski.

## Prior source and pinned API

This is the next source-specific implementation of the all-place argument in `proof/progress/receipts/completeness-work/ANCHOR-COMPLETENESS.md`, sections3–5. The previous packet constructed the actual2/3 Hensel roots and applied rational anisotropy after a rational homogeneous zero. This packet supplies every other local place before exposing exactly the remaining global theorem.

Read the pinned Mathlib `FieldTheory/Finite/Basic.lean` theorem `FiniteField.exists_root_sum_quadratic`: it requires a finite integral domain of odd cardinality and two polynomials of degree exactly2; its proof is the polynomial-image cardinality intersection argument. Apply it toX² and6X²−2 overZModp for primep≥5. The coefficient6 is proved nonzero and both polynomial degrees are verified. The result is an actual pairx,y withx²+6y²=2. Their standard integer lifts retain the exact divisibility byp ofx²+6y²−2.

## Actual p-adic lift and every target

For each such prime, defineF(Z)=x²+6y²−2Z² overZp. AtZ=1, the residual has norm<1 by the actual integer divisibility. The derivative is−4, whose norm is1 sincep≥5. The pinned genuine `hensels_lemma` therefore givesz withF(z)=0 andnorm(z−1)<1. This last inequality provesz≠0. Casting the same integerx,y and liftedz intoQp gives an actual nonzero isotropic vector forq=x²+6y²−2z².

For any targetc inQp, putt=−(c+2)/(4z). Then

q(tx,ty,1+tz)−c = t²q(x,y,z)−(4zt+c+2) = 0.

This represents every target at everyp≥5, with no exclusion of primes in the target's numerator or denominator. No reduction-order or selected-contact-prime theorem is substituted for this universal local statement.

The real place uses the exact isotropic vector(sqrt2,0,1) and the same explicit line formula, representing every real target.

## Same actual prepared ratio and global boundary

`ActualAnchorAllPlaces318.finite_represents` splits all primes into2,3,andp≥5. At2/3 it consumes the predecessor's actual fixed-label ratio and genuine Hensel square roots. At every other prime it uses the universal representation just constructed. `LocallyRepresented` quantifies over the real place and every primep with its actualQp field, not a finite exceptional set.

`actual_all_places` supplies this property for the literal ratio on the prepared beta/scalar/Lucas labels at any scale3^N, includingN=2^16. The global input is precisely `LocalGlobalPrinciple`: for any rationalc represented by this ternary form over every completion, there exists a nonzero rational homogeneous zero ofX²+6Y²−2Z²−cT². It is explicitly a theorem premise. Its specialization is the remaining Hasse–Minkowski step; this packet does not prove it. Thec=0 case causes no inconsistency in this formulation, sinceT=1 andX=Y=Z=0 is then a nonzero homogeneous zero.

The predecessor's rational anisotropy forces the resultingT≠0 and constructs the exact current-scale Anchor. `PreparedAllPlaceSource318.current_source_prepared_all_places` keeps all fixed labels, signs, real bounds, original CRT constraints and the sameh. Four actual two-twist realizations then imply the literal current-scale full288-row HasSolution, conditional on the clearly exposed global theorem. The caller no longer supplies a separate source-specific homogeneous zero.

## Open work and verification

Still open: the quadratic-form LocalGlobalPrinciple proof, other scalar support-prime preparation, three detector local preparations, simultaneous prime/ray selection and actual rational two-twist point producers. The all-place local input to the Anchor's global theorem is now constructed rather than asserted.

107 predecessor sources are byte-identical, including the inherited targeted normalization operation-spine repair; four new finite1,000,000-heartbeat sources give111modules/150baseline dependencies. Exact symbolic checks verify the hyperbolic-line identity, Hensel residual/derivative and real isotropic vector; finite prime enumeration is only a sanity check. Source-policy/dependency,11packet tests,audit selftests and SHA checks are structural. Hosted kernel checks and distinct bounded review remain separately required.

## Generic target-field constructor revision

Exact hosted run42603720675 at a51868a preserves the failure of the prior primitive-instance revision. Both typed first_curve and second_curve helpers pass. Their supplied curve-proof arguments at firstPoint line95 and secondPoint line103 still expand concrete tower fourth powers during definitional comparison against ReciprocalDouble318.point's generic Field argument, hitting the unchanged deterministic1M budget. Diagnostic counts include300k npowRec and1.3M quadratic projections. This version preserves110sources and revises only NormalizedPointSigns318: target_curve, targetPoint, targetFlip and their sign lemmas are elaborated once with an abstract target Field. The entire well-typed constructor is then specialized to the same Both,base,delta,deltaBar and roots. The local concrete first_curve/second_curve helper theorems remain unchanged and diagnostic checkpoints remain. Private transport and the concrete reciprocal-flip helper are replaced by their identical generic versions; there are no downstream references to those old helper names. The actual public points and involution keep the same definitions after unfolding, coordinates, field operations and mathematical premises. No normalization constant, source object, sign, arbitrary producer premise or finite heartbeat budget changes. This repair attempt is subject to hosted validation, not a claim that the deterministic limit is solved.

Exact tested107 source bytes and full evidence are preserved. The111 predecessor contains the byte-identical failing NormalizedPointSigns318 module. No local Lean/build was run.
