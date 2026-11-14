# Independent OriginalAffineLineDualFrame318 source review

No source-level blocker found in the exact reviewed state. This is source/provenance review only, not a hosted candidate pass, kernel acceptance, whole-packet acceptance or declaration audit. No local Lean/Lake or user computer was used. Successor metadata/propagation requires its own review.

## Observed frontier and intended telescope
Own hosted RESULT records FiniteProjectiveDualFrame passing (1.417s), then OriginalAffineLineDualFrame failing (1.467s). The exact log has the two malformed morphism-family binders, their downstream proof cascades, and Module R synthesis failure on the unfolded section carrier. Parenthesizing ι → (M ⟶ N) and the reverse family restores the intended family of morphisms for every finite index type; it does not restrict any object or index. The generic proof still uses exactly additive-functor map_sum/map_comp and cancellation by the same e,u. Explicit CategoryTheory.Functor.map_id selects the categorical identity law. Its concrete elaboration still requires hosted confirmation.

## Same bundled sections, full finite retract
The four explicit ModuleCat.ofHom X/Y arguments name the original moduleSpecΓFunctor section object with its stored R action and the original coefficient ring R. Pinned ModuleCat.Basic's ofHom and hom_ofHom/comp/id definitions support that exact route. No replacement Module instance, new scalar action, rank-one basis or free-line assumption is introduced. out is canonicalIso.inv followed by tilde of the original frame out and tildeSelf.hom; back is the exact inverse-side sequence. The full Fin(moduleFrame.n) sum, including possible empty index, is retained.

The added hom_sum/hom_id rewrite bridges the categorical sum to the existing Frame.total equality of linear maps. Pinned hom_sum is a theorem rather than a definitional sum reduction. This is a supporting repair in the previously blocked total application, not a separately observed failure. The composition order becomes back.comp out exactly as Frame.total requires.

## Exact downstream object
OriginalAffineLineLocalHOne.eq_zero consumes these same out/back maps and total on the original L.object, forgets only scalars, and applies ExtFiniteRetractVanishing on each affine open. Its own IsDomain R restriction is unchanged and is not added to this generic finite-frame theorem. No rationalization, smaller cover or global trivialization is introduced. Consumer elaboration is not asserted by this review. The contract accurately discloses the syntax/telescope correction and supporting sum projection.

## Exact bindings

- OriginalAffineLineDualFrame318.lean: before `7eb0e2ca44e95d362b2f13e5ebe25cc4237d910f43f626acf1e4bfb60d53dccc`; reviewed `3fbdde87897c3d9717a66718a699166919fbfd69142db085cc350bdc4b00ec42`.

The companion manifest binds own logs/RESULTs, Git-pinned predecessor intakes, and primary/consumer evidence. All pre-existing option lines are byte-identical.
