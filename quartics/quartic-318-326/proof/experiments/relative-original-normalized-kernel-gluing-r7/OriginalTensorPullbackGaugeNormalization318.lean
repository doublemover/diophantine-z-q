module
public import OriginalModuleFrameRatio318
public section
noncomputable section
namespace OriginalTensorPullbackGaugeNormalization318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) (M N : Y.Modules) (U : Y.Opens)
  (em : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
  (en : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ N.restrict U.ι)
@[expose] def sourceFrame :=
  LinePullbackFrames318.frame p (IntrinsicTensorSheaf318.tensor M N) U
    (TensorLineLocalFrame318.frame M N U em en)
@[expose] def targetFrame :=
  TensorLineLocalFrame318.frame ((Scheme.Modules.pullback p).obj M)
    ((Scheme.Modules.pullback p).obj N) (p ⁻¹ᵁ U)
    (LinePullbackFrames318.frame p M U em) (LinePullbackFrames318.frame p N U en)
variable (a b : Γ(U.toScheme,⊤)ˣ)
local notation "s" => StructureLineAutomorphisms318.iso (p ⁻¹ᵁ U).toScheme
  (OriginalFramePullbackUnits318.units (LinePullbackFrames318.chartMap p U) (a*b))
/-- The source-side full chart frame changes by the actual pulled product
unit, not by a unit inferred from an abstract isomorphism class. -/
lemma source_action :
    sourceFrame p M N U (StructureLineAutomorphisms318.iso U.toScheme a ≪≫ em)
      (StructureLineAutomorphisms318.iso U.toScheme b ≪≫ en)=
    s ≪≫ sourceFrame p M N U em en := by
  unfold sourceFrame
  rw [OriginalTensorUnitFrameAction318.frame,OriginalChartFrameUnitPullback318.action]
/-- The target-side tensor of pulled frames changes by EXACTLY the same
unit. Native regular-function pullback preserves the product. -/
lemma target_action :
    targetFrame p M N U (StructureLineAutomorphisms318.iso U.toScheme a ≪≫ em)
      (StructureLineAutomorphisms318.iso U.toScheme b ≪≫ en)=
    s ≪≫ targetFrame p M N U em en := by
  unfold targetFrame
  rw [OriginalChartFrameUnitPullback318.action,OriginalChartFrameUnitPullback318.action,
    OriginalTensorUnitFrameAction318.frame,map_mul]
end OriginalTensorPullbackGaugeNormalization318
