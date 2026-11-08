module
public import TensorLineLocalFrame318
public import LineFrameAdjunction318
public section
noncomputable section
namespace TensorLineCoordinateMaps318
open AlgebraicGeometry CategoryTheory Opposite
open IntrinsicTensorSheaf318
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M N:X.Modules) (U:X.Opens)
    (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
    (f:SheafOfModules.unit U.toScheme.ringCatSheaf≅N.restrict U.ι)
/-- The original coordinate morphism on an arbitrary ambient open sends an
actual pure tensor to the product of the two original coordinate sections. -/
lemma coordinate_pure (W:X.Opens) (m:Γ(M,W)) (n:Γ(N,W)):
    (LineFrameAdjunction318.coordinate (tensor M N) U (TensorLineLocalFrame318.frame M N U e f)).val.app (op W)
      (pure M N W m n)=
      ((LineFrameAdjunction318.coordinate M U e).val.app (op W) m:Γ(U.toScheme,U.ι⁻¹ᵁW))*
        ((LineFrameAdjunction318.coordinate N U f).val.app (op W) n:Γ(U.toScheme,U.ι⁻¹ᵁW)):=by
  rw [LineFrameAdjunction318.coordinate_app,pure_restrict]
  rw [TensorLineLocalFrame318.inverse_pure]
  rfl
end TensorLineCoordinateMaps318
