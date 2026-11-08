module
public import IntrinsicChartNaturality318
public section
noncomputable section
namespace ScaledGlobalSectionRestriction318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X:Scheme.{u}} {S:Type u} [CommRing S]
    (M:X.Modules) (j:Spec (CommRingCat.of S)⟶X) [IsOpenImmersion j]
@[expose] def scalar (a:S):Γ(X,j ''ᵁ ⊤):=
  (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a)
@[expose] def scaled (a:S) (s:Γ(M,⊤)):Γ(M,j ''ᵁ ⊤):=
  scalar j a • M.presheaf.map (homOfLE le_top).op s

variable {T:Type u} [CommRing T] (f:S→+*T)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]

theorem restrict (a:S) (s:Γ(M,⊤)):
    M.presheaf.map (homOfLE (OpenChartSections318.imageLE
      (Spec.map (CommRingCat.ofHom f)) j)).op (scaled M j a s)=
    scaled M (Spec.map (CommRingCat.ofHom f)≫j) (f a) s:=by
  unfold scaled scalar
  rw [Scheme.Modules.map_smul,OpenChartSections318.affine_restriction]
  congr 1
  exact (CategoryTheory.Functor.map_comp_apply _ _ _ _).symm

/-- The actual full-open restriction of a scalar times a global section,
through the specified equality of Scheme chart routes. -/
theorem restrict_to (k:Spec (CommRingCat.of T)⟶X) [IsOpenImmersion k]
    (route:Spec.map (CommRingCat.ofHom f)≫j=k) (h:k ''ᵁ ⊤≤j ''ᵁ ⊤)
    (a:S) (s:Γ(M,⊤)):
    M.presheaf.map (homOfLE h).op (scaled M j a s)=scaled M k (f a) s:=by
  subst k
  exact restrict M j f a s
end ScaledGlobalSectionRestriction318
