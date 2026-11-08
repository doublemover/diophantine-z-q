module
public import CocycleGaugeIso318
public import FifthLineExtractedCocycle318
public section
noncomputable section
namespace FifthNormGaugeIso318
open AlgebraicGeometry CategoryTheory Opposite
open FifthCompletedGlobal318 FifthChartNorm318
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι:Type} (U:ι→Target.Opens)
    (c d:FifthNormCocycle318.SourceCocycle U)
    (a:∀i,Γ(Model,map⁻¹ᵁU i)ˣ)
    (h:∀i j,d.transition i j=UnitTransitionCocycle318.coboundary
      (StructureUnitsSheaf318.pushedUnits map).obj U a i j*c.transition i j)
@[expose] def targetUnit (i:ι):Γ(Target,U i)ˣ:=
  FifthOpenNorm318.unitNorm.app (op (U i)) (a i)
include h in
lemma target_relation (i j:ι):
    (FifthNormCocycle318.transfer d).transition i j=
      UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units Target).obj U
        (targetUnit U a) i j*(FifthNormCocycle318.transfer c).transition i j:=by
  rw [FifthNormCocycle318.transition,h,map_mul]
  congr 1
  exact FifthNormCocycle318.coboundary U a i j
/-- Actual fixed-cover normed-line isomorphism, with precisely the norms of
the supplied original changes of source frame as coefficient multipliers. -/
@[expose] def iso:CocycleModule318.object U (FifthNormCocycle318.transfer c)≅
    CocycleModule318.object U (FifthNormCocycle318.transfer d):=
  CocycleGaugeIso318.iso U (FifthNormCocycle318.transfer c)
    (FifthNormCocycle318.transfer d) (targetUnit U a) (target_relation U c d a h)
lemma hom_coefficient (i:ι):(iso U c d a h).hom≫
    CocycleModule318.coefficient U (FifthNormCocycle318.transfer d) i=
      CocycleModule318.coefficient U (FifthNormCocycle318.transfer c) i≫
        CocycleGaugeMaps318.scale U (targetUnit U a) i:=
  CocycleGaugeIso318.hom_coefficient _ _ _ _ _ i
lemma inv_coefficient (i:ι):(iso U c d a h).inv≫
    CocycleModule318.coefficient U (FifthNormCocycle318.transfer c) i=
      CocycleModule318.coefficient U (FifthNormCocycle318.transfer d) i≫
        CocycleGaugeMaps318.scale U (fun i=>(targetUnit U a i)⁻¹) i:=
  CocycleGaugeIso318.inv_coefficient _ _ _ _ _ i
lemma hom_inv:(iso U c d a h).hom≫(iso U c d a h).inv=𝟙 _ :=(iso U c d a h).hom_inv_id
lemma inv_hom:(iso U c d a h).inv≫(iso U c d a h).hom=𝟙 _ :=(iso U c d a h).inv_hom_id
variable (M:Model.Modules)
  (frames newFrames:∀i,SheafOfModules.unit (map⁻¹ᵁU i).toScheme.ringCatSheaf≅M.restrict (map⁻¹ᵁU i).ι)
/-- Two actual frames of the unchanged original source line on the same
entire inverse-image cover produce genuinely isomorphic normed target lines. -/
@[expose] def ofOriginalFrames:
    CocycleModule318.object U (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map M U frames))≅
    CocycleModule318.object U (FifthNormCocycle318.transfer
      (InverseImageLineCocycle318.cocycle map M U newFrames)):=
  iso U _ _ (LineFrameGauge318.unit M (fun i=>map⁻¹ᵁU i) frames newFrames)
    (InverseImageLineCocycle318.gauge_equation map M U frames newFrames)
end FifthNormGaugeIso318
