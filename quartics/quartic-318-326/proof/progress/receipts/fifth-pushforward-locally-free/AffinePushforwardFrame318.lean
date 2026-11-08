module
public import AffineSpecFreePushforward318
public import AffinePullbackStructure318
public import ModuleFrameTransport318
public section
noncomputable section
namespace AffinePushforwardFrame318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 650000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) [IsAffineHom f] (U:Y.Opens) (hU:IsAffineOpen U)
local instance sectionAlgebra:Algebra Γ(Y,U) Γ(X,f⁻¹ᵁU):=(f.app U).hom.toAlgebra
variable {ι:Type u} (bs:Module.Basis ι Γ(Y,U) Γ(X,f⁻¹ᵁU))
/-- Genuine affine-Spec frame for the original pushforward, using the actual
cartesian chart comparison and the original section-algebra basis. -/
@[expose] def specFrame:SheafOfModules.free (R:=(Spec Γ(Y,U)).ringCatSheaf) ι≅
    (PushforwardStructureSheaf318.object f).restrict hU.fromSpec:=
  AffineSpecFreePushforward318.iso Γ(Y,U) Γ(X,f⁻¹ᵁU) bs ≪≫
    (AffinePullbackStructure318.iso f U hU).symm
/-- Genuine free sheaf frame on the original open subscheme, not just a
basis on its affine spectrum or its global section module. -/
@[expose] def frame:SheafOfModules.free (R:=(U:Scheme).ringCatSheaf) ι≅
    (PushforwardStructureSheaf318.object f).restrict U.ι:=
  ModuleFrameTransport318.fromSpec (PushforwardStructureSheaf318.object f) U hU ι
    (specFrame f U hU bs)
lemma frame_hom_inv:(frame f U hU bs).hom≫(frame f U hU bs).inv=𝟙 _ :=
  (frame f U hU bs).hom_inv_id
lemma frame_inv_hom:(frame f U hU bs).inv≫(frame f U hU bs).hom=𝟙 _ :=
  (frame f U hU bs).inv_hom_id
end AffinePushforwardFrame318
