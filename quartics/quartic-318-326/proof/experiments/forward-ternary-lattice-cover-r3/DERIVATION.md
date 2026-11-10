# Actual squarefree ternary-congruence lattice cover

All 263 predecessor sources are byte-identical. This three-source span constructs a large-prime obstruction-tail ingredient from the original ternary form R=κw²−2xz.

TernaryQuadraticLineCover318 explicitly covers R=0 over each odd residue field with q finite-slope/infinity projective directions (q+1 total). The finite-slope line is (a,κt²a/2,ta); the infinity line is (0,a,0). Every original residue vector is reconstructed, including the zero vector. Each line is the kernel of an explicit TWO-coordinate additive code with an actual right inverse.

TernaryCongruenceLattices318 takes the original integer-coordinate preimage of each line. Its residue code is proved surjective by actual integer lifts. The primary quotient-kernel equivalence gives the exact additive index p². Original integer divisibility p|κw²−2xz is equivalent to membership in one of these actual lattices; no isotropic direction is supplied by the caller.

SquarefreeTernaryLatticeCover318 constructs simultaneous integer lifts using the existing actual CRT ring equivalence. Its global residue code is surjective onto the product of the two-coordinate local spaces. Every resulting original integer congruence lattice has index (product p)². The actual squarefree divisibility condition is exactly the union of these lattices. The number of indexed lattices is product(p+1)<=2^omega(q)q, stronger than the manuscript's coarse9^omega(q)q cover bound. Empty prime index sets are included.

## Assumptions and boundary
Primes are pairwise distinct, odd and avoid κ. The lattice is an actual additive subgroup of Z³; exact finite index is established. No Euclidean successive-minima bound, reduced basis, rectangular lattice-point estimate, large-prime tail estimate or global Gaussian prime production is claimed from index alone. Those geometric/counting producers remain next. This formalizes the original ternary congruence, not a substitute quadratic form with an assumed isomorphism.

## Evidence
Pinned primary GroupTheory/Index index_eq_card and QuotientAddGroup.quotientKerEquivOfSurjective read. Exact finite tests:34 local field/coefficient systems,42286 original local vectors,368 local surjective codes;10 squarefree systems,111078 original global vectors and46 exact global code indices. Negative controls show the actual infinity line cannot be dropped and κ=0 invalidates this cover. Static source policy and266/222 dependency closure pass. No local Lean compilation.

## Immutable hosted flow-derivative followup
The hosted replay passed the preceding rho/v repairs. It still failed the two flow derivative lemmas because simp-based transport retained different real additive/module instance presentations and pointwise/function-composition forms. This successor changes only those two proof bodies: explicitly change both the composed derivative and the goal to the literal same flow-coordinate functions and coefficients, then use the direct proof. The v coefficient identity is rewritten before that transport. The existing scoped elaborator transparency setting is unchanged. Definitions, derivative statements, coefficients, clocks, maps and resource budgets are unchanged. The exact hosted diagnostic is preserved under hosted-failure-fe17720f. No local Lean compilation.

## Independent binder-scope correction
The reviewer identified six proof-only section-variable omissions in SquarefreeTernaryLatticeCover318. Narrow includes now retain hp/hd for integer_residue_lift and product_divisor_iff; hd for global_code_surjective,lattice_index,divisor_iff_lattice; hp for parameter_bound. Includes precede doccomments where applicable. These are the actual prime/distinctness hypotheses already used in every proof and supplied at existing call sites. No new mathematical assumption or source replacement is introduced. The preceding hosted flow-transport repair is retained byte-for-byte.
