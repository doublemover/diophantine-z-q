# OriginalAffineLineLocalHOne318: exact functorial finite-identity transport

## Observed scope

Hosted run 43572239136 at 52ab6e7faba5ec87dd4a1aa9d6cadcaef66aebca, positive r70 own artifact 14105032973, verifies the repaired OriginalAffineLineDualFrame318 (1.968s) and first fails OriginalAffineLineLocalHOne318 (3.873s). After the existing composition/sum simplification, the residual goal is precisely F.map (∑ i, out R L i ≫ back R L i) = 𝟙 (additiveLine R L). The original total and unqualified Functor.map_id simp entries were unused. No subsequent error is assumed.

## Required inputs and actual objects

The consumed ExtFiniteRetractVanishing318.eq_zero requires an actual finite identity decomposition of the SAME additive sheaf, through acyclic objects, for every index. The actual index set remains Fin (OriginalAffineLineDualFrame318.moduleFrame R L).n; it is not reduced to one generator or a rank-one basis. The moduleFrame is the finite dual frame of the original section module. out and back remain the genuine original structure-line morphisms through the unchanged tilde counit and tildeSelf.

The actual functor is F = SheafOfModules.toSheaf (Spec R).ringCatSheaf, forgetting only the original scalar action. additiveLine is its image of L.object. The isomorphism e = additiveUnitIso R is unchanged, identifying the image of the original structure line with StructureAdditiveSheaf318.sheaf (Spec R). All opens, carriers and restriction maps remain those of the same Spec R and actual original sheaf; no auxiliary carrier, topology or scalar structure is substituted.

## Changed application and exact direction

The existing simp only list continues to remove e.hom ≫ e.inv and combine F.map compositions and the complete finite sum. Instead of asking simp to discover the imported total and map-id applications in one pass, the candidate applies congrArg to the typed function (fun f : L.object ⟶ L.object => F.map f) and the exact theorem OriginalAffineLineDualFrame318.total R L. It then composes that equality with CategoryTheory.Functor.map_id F L.object. The two equalities run from the functor image of the full original finite sum to F.map (𝟙 L.object), then to the identity of its actual functor image. This is the same required identity, not an altered transition map or a new decomposition.

## Quantifiers and consuming passage

For every R : CommRingCat.{0} with IsDomain R, every original line L, every U : (Spec R).Opens, every IsAffineOpen U proof, and every x in the original additiveLine.H' 1 U, the conclusion remains x = 0. All definitions and the final ExtFiniteRetractVanishing318.eq_zero application are byte-identical. The structure-sheaf vanishing input is still LocalAffineStructureHOne318.eq_zero U hU for every finite index and every class. OriginalAffineLineSectionLifting318.surjective consumes this exact theorem at U = ⊤ in its boundary-class argument, alongside the unchanged OriginalLineRestrictionAdditive318 identification; subsequent original affine/open lifting remains on the same sheaf.

## Evidence and verification limits

Only this proof segment changes in the 107-module ordered closure; the other 106 source files, all imports and all resource options are byte-identical. Primary producers and immediate consumer are retained alongside the exact own RESULT/logs and before/after/diff. Distinct independent application and propagation reviews are required for this revised staged route. No local Lean/Lake run, increased cap, kernel acceptance, recursive-axiom audit or full arithmetic theorem claim is made. Hosted elaboration remains pending.
