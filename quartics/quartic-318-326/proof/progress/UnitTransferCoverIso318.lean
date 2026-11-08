module
public import UnitTransferGaugeIso318
public import InverseImageLineRefinement318
public import CocycleRefinementIso318
public section
noncomputable section
namespace UnitTransferCoverIso318
open AlgebraicGeometry CategoryTheory UnitCocycleRefinement318 UnitTransferGaugeIso318
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y)
    (unitMap:StructureUnitsSheaf318.pushedUnits f⟶StructureUnitsSheaf318.units Y)
    (M:X.Modules) {ι κ:Type u} (U:ι→Y.Opens) (V:κ→Y.Opens)
    (e:∀i,SheafOfModules.unit (f⁻¹ᵁU i).toScheme.ringCatSheaf≅M.restrict (f⁻¹ᵁU i).ι)
    (d:∀j,SheafOfModules.unit (f⁻¹ᵁV j).toScheme.ringCatSheaf≅M.restrict (f⁻¹ᵁV j).ι)
abbrev leftTarget:=refine (transfer f unitMap U (InverseImageLineCocycle318.cocycle f M U e))
  (common U V) Prod.fst (fun _=>inf_le_left)
abbrev rightTarget:=refine (transfer f unitMap V (InverseImageLineCocycle318.cocycle f M V d))
  (common U V) Prod.snd (fun _=>inf_le_right)
lemma left_eq:
    transfer f unitMap (common U V) (InverseImageLineRefinement318.leftCocycle f M U V e)=
      leftTarget f unitMap M U V e:=map_refine unitMap.hom _ _ _ _
lemma right_eq:
    transfer f unitMap (common U V) (InverseImageLineRefinement318.rightCocycle f M U V d)=
      rightTarget f unitMap M U V d:=map_refine unitMap.hom _ _ _ _
/-- Comparison on the literal whole common cover with the actual original
source-frame gauge units. -/
@[expose] def commonIso:CocycleModule318.object (common U V) (leftTarget f unitMap M U V e)≅
    CocycleModule318.object (common U V) (rightTarget f unitMap M U V d):=
  eqToIso (congrArg (CocycleModule318.object (common U V)) (left_eq f unitMap M U V e).symm)≪≫
  UnitTransferGaugeIso318.iso f unitMap (common U V)
    (InverseImageLineRefinement318.leftCocycle f M U V e)
    (InverseImageLineRefinement318.rightCocycle f M U V d)
    (InverseImageLineRefinement318.unit f M U V e d)
    (InverseImageLineRefinement318.equation f M U V e d)≪≫
  eqToIso (congrArg (CocycleModule318.object (common U V)) (right_eq f unitMap M U V d))
variable (hU:(⊤:Y.Opens)≤⨆i,U i) (hV:(⊤:Y.Opens)≤⨆j,V j)
/-- Actual module-sheaf comparison across two independently supplied full
covers, not equality of their presentation records. -/
@[expose] def iso:
    CocycleModule318.object U (transfer f unitMap U (InverseImageLineCocycle318.cocycle f M U e))≅
    CocycleModule318.object V (transfer f unitMap V (InverseImageLineCocycle318.cocycle f M V d)):=
  CocycleRefinementIso318.iso U _ (common U V) Prod.fst (fun _=>inf_le_left)
    (common_cover U V hU hV)≪≫commonIso f unitMap M U V e d≪≫
  (CocycleRefinementIso318.iso V _ (common U V) Prod.snd (fun _=>inf_le_right)
    (common_cover U V hU hV)).symm
lemma hom_inv:(iso f unitMap M U V e d hU hV).hom≫(iso f unitMap M U V e d hU hV).inv=𝟙 _ :=
  (iso f unitMap M U V e d hU hV).hom_inv_id
lemma inv_hom:(iso f unitMap M U V e d hU hV).inv≫(iso f unitMap M U V e d hU hV).hom=𝟙 _ :=
  (iso f unitMap M U V e d hU hV).inv_hom_id
end UnitTransferCoverIso318
