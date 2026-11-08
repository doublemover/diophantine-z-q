module
public import StructureLineCocycleIso318
public import FifthNormChosenSourceIso318
public section
noncomputable section
namespace FifthNormUnit318
open AlgebraicGeometry CategoryTheory
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι:Type} (U:ι→Target.Opens)
@[expose] def sourceFrames (i:ι):
    SheafOfModules.unit (map⁻¹ᵁU i).toScheme.ringCatSheaf≅
      Scheme.Modules.restrict (SheafOfModules.unit Model.ringCatSheaf) (map⁻¹ᵁU i).ι:=
  StructureLineFrames318.frame Model (map⁻¹ᵁU i)
lemma source_cocycle_eq:
    InverseImageLineCocycle318.cocycle map (SheafOfModules.unit Model.ringCatSheaf) U
      (sourceFrames U)=UnitCocycleOne318.one (StructureUnitsSheaf318.pushedUnits map).obj U:=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact StructureLineFrames318.inverseImage_transition_one Model map U i j
lemma norm_cocycle_eq:
    FifthNormCocycle318.transfer (InverseImageLineCocycle318.cocycle map
      (SheafOfModules.unit Model.ringCatSheaf) U (sourceFrames U))=
      UnitCocycleOne318.one (StructureUnitsSheaf318.units Target).obj U:=by
  rw [source_cocycle_eq]
  exact UnitCocycleOne318.map_one FifthOpenNorm318.unitNorm U
/-- The normed line from identity structure-sheaf frames is genuinely the
original target structure module, with explicit inverse isomorphisms. -/
@[expose] def fixedIso (hc:(⊤:Target.Opens)≤⨆i,U i):
    CocycleModule318.object U (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map (SheafOfModules.unit Model.ringCatSheaf)
        U (sourceFrames U)))≅SheafOfModules.unit Target.ringCatSheaf:=
  CocycleEqualityTransport318.iso U (norm_cocycle_eq U)≪≫
    (StructureLineCocycleIso318.iso Target U hc).symm
lemma fixed_hom_inv (hc:(⊤:Target.Opens)≤⨆i,U i):
    (fixedIso U hc).hom≫(fixedIso U hc).inv=𝟙 _ :=(fixedIso U hc).hom_inv_id
lemma fixed_inv_hom (hc:(⊤:Target.Opens)≤⨆i,U i):
    (fixedIso U hc).inv≫(fixedIso U hc).hom=𝟙 _ :=(fixedIso U hc).inv_hom_id
variable (M:Model.Modules) (e:M≅SheafOfModules.unit Model.ringCatSheaf)
    {α:Type} (A:α→Model.Opens) (hA:(⊤:Model.Opens)≤⨆i,A i)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅M.restrict (A i).ι)
/-- Any supplied genuine trivialization of the original source line gives
an actual trivialization of its constructed norm line, independently of the
chosen initial covering frames. No class or Picard identification is used. -/
@[expose] def chosenIso:
    FifthNormLineObject318.object M A hA eA≅SheafOfModules.unit Target.ringCatSheaf:=
  FifthNormSourceIso318.iso e (FifthLineTargetCover318.neighborhood M A hA eA)
    (FifthLineTargetCover318.frame M A hA eA)
    (sourceFrames (FifthLineTargetCover318.neighborhood M A hA eA))≪≫
  fixedIso (FifthLineTargetCover318.neighborhood M A hA eA)
    (FifthLineTargetCover318.cover_top M A hA eA)
lemma chosen_hom_inv:(chosenIso M e A hA eA).hom≫(chosenIso M e A hA eA).inv=𝟙 _ :=
  (chosenIso M e A hA eA).hom_inv_id
lemma chosen_inv_hom:(chosenIso M e A hA eA).inv≫(chosenIso M e A hA eA).hom=𝟙 _ :=
  (chosenIso M e A hA eA).inv_hom_id
end FifthNormUnit318
