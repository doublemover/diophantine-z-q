# Changed application comparison (source-level candidate)

## Exact inputs and domains
The affine lift still quantifies every commutative complex algebra S, arbitrary t:S and all four z:Fin 4→S satisfying the literal four equations. The variable index remains Option (Fin 4): none maps to t, every some k maps to z k. The corrected `Option.elim k t z` supplies the index first according to Lean v4.35.0; this repairs an ill-typed public formula, not a restricted substitute. The same Ideal.span (Set.range equation) is killed, the same quotient algebra is consumed by pointEquiv, and Algebra.algebraMap_self_apply identifies the original complex coefficients with themselves. No branch point, including a repeated value of b, is excluded or added.

The metric is on exactly Prod ComplexVectors ℂ, the intended meaning of the malformed compact product syntax. Weight, exponent, positive Riemann form, lattice factor, norm and translation action are unchanged. The corrected signatures therefore retain the identical zero-locus and action-invariance obligations; no positivity condition is removed.

The order action remains on the full subgroup of points killed by integer 3 in the original period quotient. Additivity is evaluated at x.val and y.val in that ambient quotient, not at a second torsion carrier. The marking is the existing AddEquiv.ofBijective quotientToTorsion. The pinned generated ofBijective_apply lemma and local quotientToTorsion_mk expose its original-order representatives. Surjectivity of moduloThree.mk' still covers every class, and thirdPeriod_mul still proves left multiplication by the same original order endomorphism with no lost scalar.

## Consumers and historical scope
The affine point equivalence, metric descent, regular quotient action, faithful marking and full-level statement all consume these same objects. Imports, statement assumptions, theorem order and all unmodified modules remain frozen. The source hashes and exact-copy closure are in intake.json and COPY_BINDINGS.json. These are newly exposed elaboration blockers in run 43503478144, not a claim that previous mathematical reasoning was absent. Reviewed predecessor repairs are carried forward byte-for-byte; their historical acceptance, if any, does not authorize these changed applications.

## Limits
No Lean compiler has run locally. The new source must receive hosted Lean checking, its declaration audit, and distinct source review. This candidate comparison is authored by the repair author and is not an independent acceptance record.
