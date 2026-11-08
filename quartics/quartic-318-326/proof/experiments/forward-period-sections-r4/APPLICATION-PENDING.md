# Period inverse sections R4: exact argument repair, pending hosted recheck

Run42471197658/head2e78fdee passed the unchanged projection module and reached the final consumer theorem. The only reported error is its use of the public PartialDiffeomorph.isLocalDiffeomorphAt lemma without the explicit model-with-corners and differentiability-order arguments. Mathlib's own localInverse_isLocalDiffeomorphAt uses dot notation with three explicit arguments before the membership proof.

The sole change supplies 𝓘(ℂ), 𝓘(ℂ), omega to that exact lemma. All definitions, theorem statements, branch maps and domains, natural/source atlases, inverse-germ proofs, imports and the unchanged projection source are otherwise byte-identical. No new inverse is selected, and no mathematical conclusion is weakened.

1. Exact source: pinned Mathlib LocalDiffeomorph.lean declaration and its own three-argument usage are source-bound.
2. Actual objects: unchanged natural period locus and actual source quotient with its independently constructed genuine-j atlas.
3. Coverage: each original period tau and every point in its actual covering inverse branch.
4. Maps: the unchanged covering localInverseAt is retained exactly; forward equality remains sourceProjection.
5. Analyticity: the original inverse-germ argument uses genuine j analytic and nonzero derivative at that exact period, with full local right-inverse equality and continuity.
6. Normalization: localBiholomorph retains the original partial equivalence, domains and maps, not an arbitrary coordinate reparameterization.
7. Final application: the public lemma consumes its real source-membership proof; exact forward function equality rewrites to sourceProjection.
8. Evidence: prior strict failure is separately frozen. Only source/import/pin checks are newly performed; this revision's Lean check, recursive audit and independent review remain pending. No local compile or dispatch.
9. Boundary: only the admissible open excludes j=0 and1728. No exceptional-j/cusp extension, scheme-analytification functor or D210 Jacobian/PEL identification. The separately successful ambient packet is not repeated here.
