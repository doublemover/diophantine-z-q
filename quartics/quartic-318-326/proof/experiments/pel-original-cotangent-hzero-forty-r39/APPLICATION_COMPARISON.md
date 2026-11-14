# Changed PEL application contracts: run 43519890754

Status: source repair candidate; hosted Lean required. No compiler was run locally. This is an author comparison, not independent acceptance.

## FourRootAffineCoordinateRing318.lift_coordinate
The source is the exact ideal quotient of the five-variable polynomial algebra over ℂ, indexed by Option (Fin 4), by all four literal equations z_k² = t − b_k. The lift still quantifies any commutative complex algebra S, t : S and every z : Fin 4 → S satisfying all four equations. The repair changes only the evaluation proof: quotient lifting evaluated at its generating quotient class is definitionally the original MvPolynomial.aeval on X k, and the pinned aeval_X theorem returns the same index assignment. Neither the ideal-killing proof nor the lift, coordinate, point, or pointEquiv definitions change. Every none/some index, all branch values including coincident b, and downstream complex-valued points remain included. No statement, input, quotient, or scalar algebra is replaced.

## PELOriginalPolarizationMetric318.squaredNorm_action
Both namespaced actions are in scope. The intended action is the original lattice automorphy action on Prod ComplexVectors ℂ, not the real matrix representation on ComplexVectors. The statement already resolves by its type to the former; spelling its full name in the statement and simp list makes that same choice explicit. The original exponent, norm square, positive Gaussian weight, lattice phase, and translation z + l.val are unchanged. The proof still consumes the exact factor_metric identity; no exponent, positivity assumption, or object is altered.

## PELLevelThreeAlternatingPair318.original_adjoint
The quotient is the actual original order modulo 3, not a pointwise coordinate ring. Coordinates are additive integer coordinates and coordinatesEquiv is only an additive equivalence. Its custom product is the original noncommutative order multiplication. Bare reverse map_mul incorrectly targeted the additive equivalence. The replacement explicitly names the actual quotient ring hom moduloThree.mk' and its two order arguments, then applies coordinates_mul with the corresponding explicit original-coordinate pairs. The existing surjectivity reductions still cover every a in the order and every b,c in O/3O. Original Rosati involution, negative integral pairing sign, coordinates, integral_adjoint, and the full original_adjoint statement are unchanged. Downstream torsion polarization consumes the same quotient pairing and left action.

## Scope and historical comparison
These are exact newly observed or residual first-failure diagnostics from run 43519890754 on 58753ec. Previous API/parser repairs remain present and are not relabeled as newly accepted mathematical reasoning. Hosted trace and character results confirm PELThreeTorsionOrderAction318 and PELLevelThreeCoordinates318 now compile, but no whole packet has passed. The separately reviewed preventive infinity/sign API fixes below are included in this successor; no hosted failure for them is claimed. No import, module order, resource budget, public hypothesis, admission, or native evaluator changes.

# Preventive, not yet hosted-observed API repairs

These two modules lie downstream of current first failures. No hosted failure or Lean pass is claimed for either. Inclusion requires fresh independent source review.

## Normalized infinity coordinate algebra
FourRootInfinityCoordinateRing318 uses exactly Option (Fin 4) as polynomial variable indices, none for u and some k for every normalized root s k. Current pinned Option.elim requires the Option first. Supplying `fun k => Option.elim k u s` repairs only that argument order in the original aeval and ideal-kernel proof. The lift_coordinate formula now gives Option.elim k u s and its proof computes the identical quotient class by definition and aeval_X. The source inputs still include every commutative complex algebra S, all u and s, the mandatory s 0 = 1 normalization, and all four equations. No normalization/sign, equation, branch or algebra point is dropped. In particular this retains eight actual infinity signs, not the incorrect sixteen-sign unnormalized model. The point and pointEquiv still consume that same quotient and exact normalized InfinityPoints; Algebra.algebraMap_self_apply is just the namespaced pinned self-map identity.

## Original coordinate-ring sign actions
FourRootCoordinateRingSigns318 changes only three references to the fully qualified Algebra.algebraMap_self_apply. The original signs, affine/infinity quotient algebras, normalization and all automorphism formulas remain unchanged. All public statements and inputs are unchanged.

These are repeated API mismatches established by pinned primary sources and the observed affine analogue, not newly observed hosted failures. No imports, resource budgets, assumptions, admissions, maps or consumer objects change. Previous reviews are not copied as approval; this route requires its own review.
