module
public import OpenPullbackStructure318
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public section
noncomputable section
namespace AffinePullbackStructure318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) [IsAffineHom f] (U:Y.Opens) (hU:IsAffineOpen U)
/-- The original affine chart square, with the actual section map f.app. -/
lemma square:IsPullback (Spec.map (f.app U)) (hU.preimage f).fromSpec hU.fromSpec f:=by
  apply IsOpenImmersion.isPullback
  · simpa only [Scheme.Hom.appLE_eq_app] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl).symm
  · rw [hU.opensRange_fromSpec,(hU.preimage f).opensRange_fromSpec]
/-- Actual restriction of f_*O to the affine chart, not a replacement sheaf. -/
@[expose] def iso:(PushforwardStructureSheaf318.object f).restrict hU.fromSpec≅
    PushforwardStructureSheaf318.object (Spec.map (f.app U)):=
  OpenPullbackStructure318.iso (Spec.map (f.app U)) (hU.preimage f).fromSpec
    hU.fromSpec f (square f U hU)
lemma iso_component (W:(Spec Γ(Y,U)).Opens)
    (s:Γ((PushforwardStructureSheaf318.object f).restrict hU.fromSpec,W)):
    (iso f U hU).hom.app W s=
      (OpenPullbackStructure318.ringIso (Spec.map (f.app U)) (hU.preimage f).fromSpec
        hU.fromSpec f (square f U hU) W).hom s:=rfl
lemma iso_hom_inv:(iso f U hU).hom≫(iso f U hU).inv=𝟙 _ :=(iso f U hU).hom_inv_id
lemma iso_inv_hom:(iso f U hU).inv≫(iso f U hU).hom=𝟙 _ :=(iso f U hU).inv_hom_id
end AffinePullbackStructure318
