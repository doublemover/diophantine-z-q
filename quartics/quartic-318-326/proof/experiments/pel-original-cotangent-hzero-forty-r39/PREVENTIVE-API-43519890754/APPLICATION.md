# Preventive, not yet hosted-observed API repairs

These two modules lie downstream of current first failures. No hosted failure or Lean pass is claimed for either. Inclusion requires fresh independent source review.

## Normalized infinity coordinate algebra
FourRootInfinityCoordinateRing318 uses exactly Option (Fin 4) as polynomial variable indices, none for u and some k for every normalized root s k. Current pinned Option.elim requires the Option first. Supplying `fun k => Option.elim k u s` repairs only that argument order in the original aeval and ideal-kernel proof. The lift_coordinate formula now gives Option.elim k u s and its proof computes the identical quotient class by definition and aeval_X. The source inputs still include every commutative complex algebra S, all u and s, the mandatory s 0 = 1 normalization, and all four equations. No normalization/sign, equation, branch or algebra point is dropped. In particular this retains eight actual infinity signs, not the incorrect sixteen-sign unnormalized model. The point and pointEquiv still consume that same quotient and exact normalized InfinityPoints; Algebra.algebraMap_self_apply is just the namespaced pinned self-map identity.

## Original coordinate-ring sign actions
FourRootCoordinateRingSigns318 changes only three references to the fully qualified Algebra.algebraMap_self_apply. The original signs, affine/infinity quotient algebras, normalization and all automorphism formulas remain unchanged. All public statements and inputs are unchanged.

These are repeated API mismatches established by pinned primary sources and the observed affine analogue, not newly observed hosted failures. No imports, resource budgets, assumptions, admissions, maps or consumer objects change. Previous reviews are not copied as approval; this route requires its own review.
