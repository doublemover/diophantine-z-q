module
public import CocycleGaugeIso318
public import InverseImageLineCocycle318
public section
noncomputable section
namespace UnitTransferGaugeIso318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y)
    (unitMap:StructureUnitsSheaf318.pushedUnits f⟶StructureUnitsSheaf318.units Y)
    {ι:Type u} (U:ι→Y.Opens)
abbrev SourceCocycle:=UnitTransitionCocycle318.Cocycle (StructureUnitsSheaf318.pushedUnits f).obj U
@[expose] def transfer (c:SourceCocycle f U):=
  UnitTransitionCocycle318.map unitMap.hom c
variable (c d:SourceCocycle f U) (a:∀i,Γ(X,f⁻¹ᵁU i)ˣ)
    (h:∀i j,d.transition i j=UnitTransitionCocycle318.coboundary
      (StructureUnitsSheaf318.pushedUnits f).obj U a i j*c.transition i j)
@[expose] def targetUnit (i:ι):Γ(Y,U i)ˣ:=unitMap.hom.app (op (U i)) (a i)
include h in
lemma target_relation (i j:ι):
    (transfer f unitMap U d).transition i j=
      UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units Y).obj U
        (targetUnit f unitMap U a) i j*(transfer f unitMap U c).transition i j:=by
  change unitMap.hom.app (op (U i⊓U j)) (d.transition i j)=_
  rw [h,map_mul]
  congr 1
  exact UnitTransitionCocycle318.map_coboundary unitMap.hom U a i j
/-- Actual target isomorphism with the images of the original source gauge
units as its exact coefficient multipliers. -/
@[expose] def iso:CocycleModule318.object U (transfer f unitMap U c)≅
    CocycleModule318.object U (transfer f unitMap U d):=
  CocycleGaugeIso318.iso U _ _ (targetUnit f unitMap U a)
    (target_relation f unitMap U c d a h)
lemma hom_coefficient (i:ι):(iso f unitMap U c d a h).hom≫
    CocycleModule318.coefficient U (transfer f unitMap U d) i=
      CocycleModule318.coefficient U (transfer f unitMap U c) i≫
        CocycleGaugeMaps318.scale U (targetUnit f unitMap U a) i:=
  CocycleGaugeIso318.hom_coefficient _ _ _ _ _ i
lemma inv_coefficient (i:ι):(iso f unitMap U c d a h).inv≫
    CocycleModule318.coefficient U (transfer f unitMap U c) i=
      CocycleModule318.coefficient U (transfer f unitMap U d) i≫
        CocycleGaugeMaps318.scale U (fun i=>(targetUnit f unitMap U a i)⁻¹) i:=
  CocycleGaugeIso318.inv_coefficient _ _ _ _ _ i
lemma hom_inv:(iso f unitMap U c d a h).hom≫(iso f unitMap U c d a h).inv=𝟙 _ :=
  (iso f unitMap U c d a h).hom_inv_id
lemma inv_hom:(iso f unitMap U c d a h).inv≫(iso f unitMap U c d a h).hom=𝟙 _ :=
  (iso f unitMap U c d a h).inv_hom_id
variable (M:X.Modules)
    (frames newFrames:∀i,SheafOfModules.unit (f⁻¹ᵁU i).toScheme.ringCatSheaf≅M.restrict (f⁻¹ᵁU i).ι)
@[expose] def ofOriginalFrames:
    CocycleModule318.object U (transfer f unitMap U (InverseImageLineCocycle318.cocycle f M U frames))≅
    CocycleModule318.object U (transfer f unitMap U (InverseImageLineCocycle318.cocycle f M U newFrames)):=
  iso f unitMap U _ _ (LineFrameGauge318.unit M (fun i=>f⁻¹ᵁU i) frames newFrames)
    (InverseImageLineCocycle318.gauge_equation f M U frames newFrames)
end UnitTransferGaugeIso318
