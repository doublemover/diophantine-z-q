module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public section
noncomputable section
namespace PushforwardStructureSheaf318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 500000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y)
/-- The actual pushforward of the original structure sheaf, as an O_Y-module. -/
@[expose] def object:Y.Modules:=
  (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
lemma scalar (U:Y.Opens) (a:Γ(Y,U)) (s:Γ(object f,U)):
    a • s=(f.app U a)*(show Γ(X,f⁻¹ᵁU) from s):=rfl
lemma restriction {U V:Y.Opens} (i:U⟶V) (s:Γ(object f,V)):
    (object f).presheaf.map i.op s=
      X.presheaf.map (homOfLE (f.preimage_mono i.le)).op (show Γ(X,f⁻¹ᵁV) from s):=rfl
/-- Identity on actual sections, recording the precise section pullback scalar action. -/
@[expose] def sections (U:Y.Opens):
    letI:Algebra Γ(Y,U) Γ(X,f⁻¹ᵁU):=(f.app U).hom.toAlgebra
    Γ(object f,U)≃ₗ[Γ(Y,U)]Γ(X,f⁻¹ᵁU):=LinearEquiv.refl _ _
@[simp] lemma sections_apply (U:Y.Opens) (s:Γ(object f,U)):
    sections f U s=(show Γ(X,f⁻¹ᵁU) from s):=rfl
end PushforwardStructureSheaf318
