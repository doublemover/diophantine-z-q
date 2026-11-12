module
public import OpenLineSectionBasis318
public section
noncomputable section
namespace LineFrameAdjunction318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) (U:X.Opens)
    (e:SheafOfModules.unit U.toScheme.ringCatSheaf≅M.restrict U.ι)
/-- The actual original line coordinate map, adjoint to the inverse of
its specified original unit frame. -/
@[expose] def coordinate:M⟶(Scheme.Modules.pushforward U.ι).obj
    (SheafOfModules.unit U.toScheme.ringCatSheaf):=
  (Scheme.Modules.restrictAdjunction U.ι).homEquiv M
    (SheafOfModules.unit U.toScheme.ringCatSheaf) e.inv
lemma transpose:
    ((Scheme.Modules.restrictAdjunction U.ι).homEquiv M
      (SheafOfModules.unit U.toScheme.ringCatSheaf)).symm (coordinate M U e)=e.inv:=
  Equiv.symm_apply_apply _ _
lemma restriction_coordinate:
    (Scheme.Modules.restrictFunctor U.ι).map (coordinate M U e)≫
      (Scheme.Modules.restrictAdjunction U.ι).counit.app
        (SheafOfModules.unit U.toScheme.ringCatSheaf)=e.inv:=transpose M U e
/-- Every original section is first restricted to the actual intersection,
then evaluated by the original inverse frame; this is not a pointwise map. -/
lemma coordinate_app (W:X.Opens) (s:Γ(M,W)):
    (coordinate M U e).app W s=(e.inv.val.app (op (U.ι⁻¹ᵁW)))
      (M.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op s):=rfl
end LineFrameAdjunction318
