# Exact hosted derivative-comparison repair, r48

The 31a0e67e hosted replay 42838588630 stops ThreeJDerivativeComparison318 at three explicit errors. This successor changes only the proof endings in that source. evaluation_t now supplies the exact aeval_X equality after the localization lift reduction; etaleEvaluation_inclusion closes the definitional ring-hom coercion equality explicitly. derivative_unit_iff_coefficient_zero first proves derivative=0 iff analytic multiplicity is nonzero, using the actual exhaustive multiplicity theorem, then negates BOTH sides. The old rewrite had negated the wrong syntactic form and did not elaborate.

All definitions, theorem statements, maps, divisors, hypotheses, coefficients, and other Lean sources remain identical to r47. In particular evaluation includes every nonzero finite parameter and still retains -27. This is not a new global relative-differential sheaf theorem. All earlier unproved global joins remain open. Old review files, if present in inherited evidence directories, describe their historical byte sets only.

Source-policy/hash/dependency checks only; no local Lean. Hosted compilation and recursive audit pending. A distinct reviewer must accept these exact repair bytes before publication.
