module
public import TensorLineFrameCoordinates318
public import UnitCocycleProduct318
public import LineFrameCocycle318
public section
noncomputable section
namespace TensorLineCocycle318
open AlgebraicGeometry CategoryTheory
open IntrinsicTensorSheaf318
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X:Scheme.{u}} (M N:X.Modules) (U:X.Opens)
    (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
    (f:SheafOfModules.unit U.toScheme.ringCatSheaf≅N.restrict U.ι)
lemma frame_pure (Z:X.Opens) (hZ:Z≤U) (a b:Γ(X,Z)):
    OpenLineFrameCoordinates318.frame (tensor M N) U (TensorLineLocalFrame318.frame M N U e f) Z hZ (a*b)=
      pure M N Z (OpenLineFrameCoordinates318.frame M U e Z hZ a)
        (OpenLineFrameCoordinates318.frame N U f Z hZ b):=by
  apply (OpenLineFrameCoordinates318.frame (tensor M N) U (TensorLineLocalFrame318.frame M N U e f) Z hZ).symm.injective
  rw [LinearEquiv.symm_apply_apply,TensorLineFrameCoordinates318.inverse_pure,
    LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
lemma generator (Z:X.Opens) (hZ:Z≤U):
    OpenLineFrameCoordinates318.frame (tensor M N) U (TensorLineLocalFrame318.frame M N U e f) Z hZ 1=
      pure M N Z (OpenLineFrameCoordinates318.frame M U e Z hZ 1)
        (OpenLineFrameCoordinates318.frame N U f Z hZ 1):=by
  simpa only [one_mul] using frame_pure M N U e f Z hZ 1 1
variable {ι:Type v} (V:ι→X.Opens)
    (em:∀i,SheafOfModules.unit (V i).toScheme.ringCatSheaf≅M.restrict (V i).ι)
    (en:∀i,SheafOfModules.unit (V i).toScheme.ringCatSheaf≅N.restrict (V i).ι)
@[expose] def frames (i:ι):SheafOfModules.unit (V i).toScheme.ringCatSheaf≅(tensor M N).restrict (V i).ι:=
  TensorLineLocalFrame318.frame M N (V i) (em i) (en i)
/-- Actual transition multiplication on every original common subopen. -/
lemma scalar_product (i j:ι) (Z:X.Opens) (hi:Z≤V i) (hj:Z≤V j):
    FrameScalarAlgebra318.scalar
      (OpenLineFrameCoordinates318.frame (tensor M N) (V i) (frames M N V em en i) Z hi)
      (OpenLineFrameCoordinates318.frame (tensor M N) (V j) (frames M N V em en j) Z hj)=
    FrameScalarAlgebra318.scalar (OpenLineFrameCoordinates318.frame M (V i) (em i) Z hi)
      (OpenLineFrameCoordinates318.frame M (V j) (em j) Z hj)*
    FrameScalarAlgebra318.scalar (OpenLineFrameCoordinates318.frame N (V i) (en i) Z hi)
      (OpenLineFrameCoordinates318.frame N (V j) (en j) Z hj):=by
  apply Units.ext
  change (OpenLineFrameCoordinates318.frame (tensor M N) (V i) (frames M N V em en i) Z hi).symm
      (OpenLineFrameCoordinates318.frame (tensor M N) (V j) (frames M N V em en j) Z hj 1)=_
  dsimp only [frames]
  rw [generator,TensorLineFrameCoordinates318.inverse_pure]
  rfl
/-- The product transition is derived from actual tensor frames and pure
multiplication, rather than assigned to an unrelated tensor label. -/
lemma cocycle_eq:
    LineFrameCocycle318.cocycle (tensor M N) V (frames M N V em en)=
      UnitCocycleProduct318.product (LineFrameCocycle318.cocycle M V em)
        (LineFrameCocycle318.cocycle N V en):=by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact scalar_product M N V em en i j (V i⊓V j) inf_le_left inf_le_right
end TensorLineCocycle318
