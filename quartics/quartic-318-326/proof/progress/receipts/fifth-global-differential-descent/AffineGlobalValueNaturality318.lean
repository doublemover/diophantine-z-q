module
public import AffineGlobalFunction318
public section
noncomputable section
namespace AffineGlobalValueNaturality318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {R S:Type u} [CommRing R] [CommRing S]
    (j:Spec (CommRingCat.of R)⟶X) [IsOpenImmersion j]
    (f:R→+*S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]
lemma value_congr {j k:Spec (CommRingCat.of R)⟶X} [IsOpenImmersion j] [IsOpenImmersion k]
    (h:j=k) (a:Γ(X,⊤)):AffineGlobalFunction318.value j a=AffineGlobalFunction318.value k a:=by
  subst k
  rfl
lemma value_comp (a:Γ(X,⊤)):
    AffineGlobalFunction318.value (Spec.map (CommRingCat.ofHom f)≫j) a=
      f (AffineGlobalFunction318.value j a):=by
  rw [AffineGlobalFunction318.value_appTop,Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply,AffineGlobalFunction318.value_appTop]
  exact congrArg (fun g=>g (j.appTop a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
end AffineGlobalValueNaturality318
