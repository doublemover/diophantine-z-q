module
public import PrincipalBasisTransport318
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section
namespace AffinePrincipalBasis318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) (U:Y.Opens) (r:Γ(Y,U))
abbrev targetOpen:Y.Opens:=Y.basicOpen r
abbrev sourceOpen:X.Opens:=f⁻¹ᵁtargetOpen U r
@[expose,instance_reducible] def originalAlgebra:
    Algebra Γ(Y,U) Γ(X,f⁻¹ᵁU):=(f.app U).hom.toAlgebra
@[expose,instance_reducible] def localAlgebra:
    Algebra Γ(Y,targetOpen U r) Γ(X,sourceOpen f U r):=(f.app (targetOpen U r)).hom.toAlgebra
attribute [local instance] originalAlgebra localAlgebra
/-- The target principal localization restricts to the entire inverse-image open,
not an arbitrarily chosen affine part of that inverse image. -/
lemma sourceOpen_eq:sourceOpen f U r=X.basicOpen (f.app U r):=f.preimage_basicOpen r
/-- Exact transport from canonical localized modules to the original Scheme
section module on the full inverse image of the principal neighborhood. -/
@[expose] def basis (hU:IsAffineOpen U) (hV:IsAffineOpen (f⁻¹ᵁU)) {ι:Type*}
    (b:Module.Basis ι (Localization.Away r) (LocalizedModule.Away r Γ(X,f⁻¹ᵁU))):
    Module.Basis ι Γ(Y,targetOpen U r) Γ(X,sourceOpen f U r):=by
  let R:=Γ(Y,U)
  let B:=Γ(X,f⁻¹ᵁU)
  let R':=Γ(Y,targetOpen U r)
  let B':=Γ(X,sourceOpen f U r)
  let i:sourceOpen f U r⟶f⁻¹ᵁU:=homOfLE ((Opens.map f.base).monotone (Y.basicOpen_le r))
  letI:Algebra B B':=(X.presheaf.map i.op).hom.toAlgebra
  letI:Algebra R B':=((algebraMap B B').comp (algebraMap R B)).toAlgebra
  letI:IsScalarTower R B B':=IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  letI:IsScalarTower R R' B':=by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact (congrArg (fun g:Γ(Y,U)⟶B'=>g a)
      (f.naturality (homOfLE (Y.basicOpen_le r)).op)).symm
  letI:IsLocalization.Away r R':=hU.isLocalization_basicOpen r
  letI:IsLocalization.Away (algebraMap R B r) B':=
    hV.isLocalization_of_eq_basicOpen (f.app U r) i (sourceOpen_eq f U r)
  exact PrincipalBasisTransport318.basis r R' B' b
end AffinePrincipalBasis318
