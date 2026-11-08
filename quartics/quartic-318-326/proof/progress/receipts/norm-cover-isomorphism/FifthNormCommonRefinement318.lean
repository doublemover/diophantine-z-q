module
public import FifthNormGaugeIso318
public import InverseImageLineRefinement318
public section
noncomputable section
namespace FifthNormCommonRefinement318
open AlgebraicGeometry CategoryTheory
open FifthCompletedGlobal318 FifthChartNorm318
open UnitCocycleRefinement318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (M:Model.Modules) {ι κ:Type} (U:ι→Target.Opens) (V:κ→Target.Opens)
    (e:∀i,SheafOfModules.unit (map⁻¹ᵁU i).toScheme.ringCatSheaf≅M.restrict (map⁻¹ᵁU i).ι)
    (d:∀j,SheafOfModules.unit (map⁻¹ᵁV j).toScheme.ringCatSheaf≅M.restrict (map⁻¹ᵁV j).ι)
abbrev leftTarget:=refine (FifthNormCocycle318.transfer
  (InverseImageLineCocycle318.cocycle map M U e)) (common U V) Prod.fst (fun _=>inf_le_left)
abbrev rightTarget:=refine (FifthNormCocycle318.transfer
  (InverseImageLineCocycle318.cocycle map M V d)) (common U V) Prod.snd (fun _=>inf_le_right)
lemma left_eq:
    FifthNormCocycle318.transfer (InverseImageLineRefinement318.leftCocycle map M U V e)=
      leftTarget M U V e:=
  map_refine FifthSheafNorm318.norm.hom _ _ _ _
lemma right_eq:
    FifthNormCocycle318.transfer (InverseImageLineRefinement318.rightCocycle map M U V d)=
      rightTarget M U V d:=
  map_refine FifthSheafNorm318.norm.hom _ _ _ _
/-- Actual target sheaf isomorphism on the genuine common intersection
family, with units from the two original source-line frames. -/
@[expose] def iso:
    CocycleModule318.object (common U V) (leftTarget M U V e)≅
      CocycleModule318.object (common U V) (rightTarget M U V d):=
  eqToIso (congrArg (CocycleModule318.object (common U V)) (left_eq M U V e).symm)≪≫
    FifthNormGaugeIso318.iso (common U V)
      (InverseImageLineRefinement318.leftCocycle map M U V e)
      (InverseImageLineRefinement318.rightCocycle map M U V d)
      (InverseImageLineRefinement318.unit map M U V e d)
      (InverseImageLineRefinement318.equation map M U V e d)≪≫
    eqToIso (congrArg (CocycleModule318.object (common U V)) (right_eq M U V d))
lemma hom_inv:(iso M U V e d).hom≫(iso M U V e d).inv=𝟙 _ :=(iso M U V e d).hom_inv_id
lemma inv_hom:(iso M U V e d).inv≫(iso M U V e d).hom=𝟙 _ :=(iso M U V e d).inv_hom_id
end FifthNormCommonRefinement318
