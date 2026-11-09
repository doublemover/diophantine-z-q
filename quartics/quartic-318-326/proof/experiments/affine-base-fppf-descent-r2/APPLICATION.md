# Application contract

1. **Source requirements.** Pinned Mathlib QuasiCompactCover.exists_hom requires a compact base, a genuine cover for the flat morphism property, its actual quasi-compact-cover instance and stability under open precomposition. The base is affine and hence compact. Flatness has the required stability. The final fppf consumers use genuine flat, surjective, locally finitely presented arrows or genuine small fppf covering families.

2. **Constructed objects.** The finite affine cover V and its morphism r to the original singleton cover come from the actual exists_hom theorem. Its full coproduct W is the new refinement source. The map b is Sigma.desc V.cover.f, while c is Sigma.desc of the actual refinement components r.h₀. The original f and original Datum f are retained by the downstream equivalence.

3. **Coverage.** Finite V.I₀ is supplied by exists_hom and installed only for that refinement, not assumed of the original cover. Every component is an actual spectrum, and the finite-affine-coproduct instance proves W affine. Original cover coverage proves b surjective. The family consumer retains the full original coproduct, including every index of an infinite small family, before selecting any finite affine refinement.

4. **Transition directions.** The equation c≫f=b is proved on every actual coproduct injection using r.w₀. These are exactly the factorization maps consumed by the prior refined-cover equivalence. The final component_map identifies forward pullback on each original family component through its named coproduct path and original naturality square.

5. **Hypothesis checks.** Flatness of b comes from the original sigma-cover property; affine source and target give IsAffineHom b; surjectivity comes from the original cover's joint coverage. Fpqc arrows get the quasi-compact-cover instance from their actual quasi-compactness. Fppf arrows instead get it from openness of flat locally finitely presented maps, so no quasi-compactness or affineness of their sources is required.

6. **Consumer identity.** The selected Refinement bundle retains W,b,c and their exact factorization. The equivalence's forward functor is the same original canonical f-pullback, not pullback along the refinement. The family endpoint uses Datum of the full actual coproduct covering arrow; the per-component comparison proves its maps match each original component rather than a finite selected subfamily.

7. **Scalars and normalization.** All descent comparisons and units are unchanged187-source producers preserving original sheaf maps and double equations. Coproduct injections and paths are explicit, with no scalar adjustment, replacement transition or quotient-level recovery. The choice of a refinement does not change the forward functor.

8. **Downstream boundary.** This supplies genuine categorical original line descent for fppf arrows and full-coproduct fppf family presentations over affine bases. General non-affine-base local assembly, equivalence with a separately indexed family-datum presentation, represented Picard/Jacobian and arithmetic conclusions remain separate. The actual fppf topology is not replaced by a topology generated only by a guessed cover class.

9. **Evidence and acceptance.** The187 producer files are unchanged copies of refined-cover-categorical-descent-r3. Four sources are new; pinned primary-source reads and content hashes are recorded in PRIMARY_SOURCE_READS.json. Hosted elaboration, recursive axiom audit and independently bound acceptance remain pending. Static closure/import/hash and audit-history checks do not establish mathematical proof; no local Lean compilation or global acceptance-register edit was used.

## Revision after exact3ee297e hosted replay

The exact3ee297e hosted run passes OriginalLineOverlapCoaction318 and advances to inverse composition. Its inverse-isomorphism equality retains local iso projections and functor-composition object wrappers, while the target has explicit natural-transformation applications. Normalize the five named isos, Functor.comp_obj and Iso.app_hom/app_inv in the existing finite simp set. Preserve the original actual tilde.functor objects, maps, composition theorem and all budgets. No new mathematical premise or map is introduced. Frozen predecessors and exact failure bytes are preserved. Hosted validation pending.
