module
public import FifthNormCommonRefinement318
public import CocycleRefinementIso318
public import FifthNormLineObject318
public section
noncomputable section
namespace FifthNormCoverIso318
open AlgebraicGeometry CategoryTheory
open FifthCompletedGlobal318 FifthChartNorm318 UnitCocycleRefinement318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (M:Model.Modules) {ι κ:Type} (U:ι→Target.Opens) (V:κ→Target.Opens)
    (e:∀i,SheafOfModules.unit (map⁻¹ᵁU i).toScheme.ringCatSheaf≅M.restrict (map⁻¹ᵁU i).ι)
    (d:∀j,SheafOfModules.unit (map⁻¹ᵁV j).toScheme.ringCatSheaf≅M.restrict (map⁻¹ᵁV j).ι)
    (hU:(⊤:Target.Opens)≤⨆i,U i) (hV:(⊤:Target.Opens)≤⨆j,V j)
/-- The original normed target modules on two genuine covers are related by
an actual sheaf isomorphism through their complete common refinement. -/
@[expose] def iso:
    CocycleModule318.object U (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map M U e))≅
    CocycleModule318.object V (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map M V d)):=
  CocycleRefinementIso318.iso U _ (common U V) Prod.fst (fun _=>inf_le_left)
    (common_cover U V hU hV)≪≫
  FifthNormCommonRefinement318.iso M U V e d≪≫
  (CocycleRefinementIso318.iso V _ (common U V) Prod.snd (fun _=>inf_le_right)
    (common_cover U V hU hV)).symm
lemma hom_inv:(iso M U V e d hU hV).hom≫(iso M U V e d hU hV).inv=𝟙 _:=
  (iso M U V e d hU hV).hom_inv_id
lemma inv_hom:(iso M U V e d hU hV).inv≫(iso M U V e d hU hV).hom=𝟙 _:=
  (iso M U V e d hU hV).inv_hom_id
variable {α β:Type} (A:α→Model.Opens) (B:β→Model.Opens)
    (hA:(⊤:Model.Opens)≤⨆i,A i) (hB:(⊤:Model.Opens)≤⨆j,B j)
    (eA:∀i,SheafOfModules.unit (A i).toScheme.ringCatSheaf≅M.restrict (A i).ι)
    (eB:∀j,SheafOfModules.unit (B j).toScheme.ringCatSheaf≅M.restrict (B j).ι)
/-- In particular, the two normed-line objects constructed from different
initial presentations of this same original source line are isomorphic. -/
@[expose] def chosenIso:
    FifthNormLineObject318.object M A hA eA≅FifthNormLineObject318.object M B hB eB:=
  iso M (FifthLineTargetCover318.neighborhood M A hA eA)
    (FifthLineTargetCover318.neighborhood M B hB eB)
    (FifthLineTargetCover318.frame M A hA eA) (FifthLineTargetCover318.frame M B hB eB)
    (FifthLineTargetCover318.cover_top M A hA eA) (FifthLineTargetCover318.cover_top M B hB eB)
lemma chosen_hom_inv:(chosenIso M A B hA hB eA eB).hom≫(chosenIso M A B hA hB eA eB).inv=𝟙 _:=
  (chosenIso M A B hA hB eA eB).hom_inv_id
lemma chosen_inv_hom:(chosenIso M A B hA hB eA eB).inv≫(chosenIso M A B hA hB eA eB).hom=𝟙 _:=
  (chosenIso M A B hA hB eA eB).inv_hom_id
end FifthNormCoverIso318
