# Original finite projective dual frame: explicit scalar and sum evaluation

Basis: hosted run 43564923898, head b3d76fb41c03f9194b0613eac0a9b4cb04b2576c, predecessor contact-original-positive-generators-r68, artifact 14101999728, ZIP SHA-256 8679bd602ccd23ae006f5ddd7b54d2b09286f25f5f4f642e756f3d2236616ebb. ContactOriginalWholeRestriction318 passed 67.246 s, and all subsequent checked modules through LocalAffineStructureHOne318 passed. The new first failure FiniteProjectiveDualFrame318 takes 1.922 s. Its exact own RESULT/log is retained.

## Exact failures and bounded changes

The scalar-linearity field of back leaves `a • f (Pi.single i b) = (RingHom.id R) a • f (Pi.single i b)` after the old rewrite. Replace only that proof line with `simp only [he,map_smul,RingHom.id_apply]`, exposing the identity ring homomorphism's action. Both sides still use the same scalar a and the same R-linear f; no new algebra or semilinear map is introduced.

The identity-decomposition proof fails to `change` an evaluated sum of linear maps into the sum of their evaluations. Insert `rw [LinearMap.sum_apply]` immediately after ext m. The pinned Mathlib source Mathlib/Algebra/Module/Submodule/LinearMap.lean states that evaluation of a finite sum of same-semilinearity maps equals the sum of their values. This is a theorem, not a definitional reduction. The existing change then only unfolds out, back, comp, projection and id. The remaining map_sum, Pi.single finite-sum identity and original retract equation are untouched.

## Source requirements and exact constructed module

All public declarations, imports, universe binders and assumptions remain byte-identical. projective_of_finitePresentation_flat has arbitrary R : Type u with CommRing, M : Type v with AddCommGroup and Module R M, and finite presentation plus flatness. Its proof still checks every maximal localization and is not edited. nonempty_frame uses exactly Module.Finite R M and Module.Projective R M.

The original Module.Finite.exists_comp_eq_id_of_projective R M produces a natural n, R-linear f : (Fin n → R) →ₗ[R] M and g : M →ₗ[R] (Fin n → R), with f surjective, g injective, and f.comp g = LinearMap.id. The construction keeps this same n, f and g. out i is projection i after g; back i maps r to f (Pi.single i r). Their sum of rank-one operators is proved to be the identity on the original M. No global rank-one basis or globally trivial line is asserted.

## Full index set, maps, scalars, and final identity

The full finite index Fin n is retained, including n = 0 when supplied by the source. Every m : M and every scalar a,b : R remain quantified. The sum is over all i : Fin n, not a selected subset; the existing Pi.single sum equals the exact function g m. Map order remains (back i).comp (out i), hence back after out, and the final theorem remains sum_i back_i ∘ out_i = id_M. The scalar action is the original R action with RingHom.id R, not a base change or alternate normalization. No factors, denominators, primes, exceptional cases or local conditions are introduced or discarded.

## Actual consumers

OriginalAffineLineDualFrame318.projective applies the unchanged projectivity theorem to OriginalLineAffineModel318.sections R L, using that original module's finite-presentation and flatness properties. moduleFrame chooses this exact Frame by frame. Its out/back sheaf maps transport the same module-frame maps through the unchanged tilde functor, original canonicalIso and tildeSelf; total consumes (moduleFrame R L).total with the same map order. OriginalAffineLineLocalHOne318 then forgets scalars and consumes that actual sheaf identity in ExtFiniteRetractVanishing318.eq_zero on every affine open, rather than substituting a new line. These consumers are unchanged and copied as primary evidence.

## Verification boundary

Exactly two proof-body edits are proposed, one scalar identity simplification and one finite-sum evaluation. No resource-cap change, imported module, definition, theorem statement or closure source other than FiniteProjectiveDualFrame318 changes. The 107-module closure is unchanged; the other 106 source files will remain byte-identical. Current internal review is source-level only. No local Lean/Lake, hosted pass for this candidate, kernel acceptance or full arithmetic proof claim is made. Historical approvals do not cover these changed applications. Exact source and successor propagation review must be completed separately before handoff.
