module
public import TensorLineLocalFrame318
public import LineFrameChartCoordinates318
public section
noncomputable section
namespace TensorLineFrameCoordinates318
open AlgebraicGeometry CategoryTheory Opposite
open IntrinsicTensorSheaf318
set_option maxHeartbeats 650000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M N:X.Modules) (U:X.Opens)
    (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
    (f:SheafOfModules.unit U.toScheme.ringCatSheaf≅N.restrict U.ι)
lemma image_le (W:U.toScheme.Opens):U.ι ''ᵁW≤U:=by
  simpa using U.ι.image_le_opensRange W
lemma inverse_image (W:U.toScheme.Opens) (m:Γ(M,U.ι ''ᵁW)) (n:Γ(N,U.ι ''ᵁW)):
    (OpenLineFrameCoordinates318.frame (tensor M N) U (TensorLineLocalFrame318.frame M N U e f)
      (U.ι ''ᵁW) (image_le U W)).symm (pure M N (U.ι ''ᵁW) m n)=
      (OpenLineFrameCoordinates318.frame M U e (U.ι ''ᵁW) (image_le U W)).symm m*
      (OpenLineFrameCoordinates318.frame N U f (U.ι ''ᵁW) (image_le U W)).symm n:=by
  calc
    _=(TensorLineLocalFrame318.frame M N U e f).inv.val.app (op W) (pure M N (U.ι ''ᵁW) m n):=
      LineFrameChartCoordinates318.over_inv_app _ U _ W _
    _=(fun a b:Γ(U.toScheme,W)=>a*b) (e.inv.val.app (op W) m) (f.inv.val.app (op W) n):=TensorLineLocalFrame318.inverse_pure M N U e f W m n
    _=_:=congrArg₂ (fun a b:Γ(X,U.ι ''ᵁW)=>a*b)
      (LineFrameChartCoordinates318.over_inv_app M U e W m).symm
      (LineFrameChartCoordinates318.over_inv_app N U f W n).symm
lemma inverse_pure (Z:X.Opens) (hZ:Z≤U) (m:Γ(M,Z)) (n:Γ(N,Z)):
    (OpenLineFrameCoordinates318.frame (tensor M N) U (TensorLineLocalFrame318.frame M N U e f) Z hZ).symm
      (pure M N Z m n)=
      (OpenLineFrameCoordinates318.frame M U e Z hZ).symm m*
      (OpenLineFrameCoordinates318.frame N U f Z hZ).symm n:=by
  let W:=U.ι⁻¹ᵁZ
  let R:=U.ι ''ᵁW
  have hR:R≤Z:=U.ι.image_preimage_le Z
  have hZR:Z≤R:=by
    dsimp [R,W]
    rw [LineFrameChartCoordinates318.image_preimage]
    exact le_inf hZ le_rfl
  have hp:=inverse_image M N U e f W
    (M.presheaf.map (homOfLE hR).op m) (N.presheaf.map (homOfLE hR).op n)
  have hh:=congrArg (fun a:Γ(X,R)=>X.presheaf.map (homOfLE hZR).op a) hp
  rw [map_mul,OpenLineFrameCoordinates318.inverse_natural,
    OpenLineFrameCoordinates318.inverse_natural,OpenLineFrameCoordinates318.inverse_natural] at hh
  rw [pure_restrict] at hh
  simp only [←M.presheaf.map_comp_apply,←N.presheaf.map_comp_apply,←op_comp,homOfLE_comp,
    homOfLE_refl,op_id,CategoryTheory.Functor.map_id] at hh
  exact hh
end TensorLineFrameCoordinates318
