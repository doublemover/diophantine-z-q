module
public import BothFiniteReversed318
public import MixedInputLocal318
public section
noncomputable section
namespace BothMixedFiniteLocal318
open BothInfinityAlgebra318 AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
lemma finite_coordinates (A B:R) (ψ:MixedInputLocal318.FiniteRing A B →ₐ[R] S)
    (p q r s:S)
    (hu:p=ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.u A B)))
    (hv:q=ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.v A B)))
    (hx:r*ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.y A B))=
      ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.x A B)))
    (hy:s*ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.y A B))=1) :
    let f:=ψ.comp (MixedInputLocal318.finitePair A B)
    p*f (InfinityAdditionAlgebra318.Y1 A B)=f (InfinityAdditionAlgebra318.X1 A B) ∧
    q*f (InfinityAdditionAlgebra318.Y1 A B)=1 ∧
    r*f (InfinityAdditionAlgebra318.Y2 A B)=f (InfinityAdditionAlgebra318.X2 A B) ∧
    s*f (InfinityAdditionAlgebra318.Y2 A B)=1 := by
  dsimp only
  have hy1:=congrArg ψ (MixedFiniteInput318.first_y_relation A B
    (MixedInputLocal318.finiteInput A B) (MixedInputLocal318.v_unit A B))
  have hx1:=congrArg ψ (MixedFiniteInput318.first_x_relation A B
    (MixedInputLocal318.finiteInput A B) (MixedInputLocal318.v_unit A B))
  simp only [map_mul,map_one] at hy1 hx1
  simp only [AlgHom.comp_apply,InfinityAdditionAlgebra318.X1,InfinityAdditionAlgebra318.Y1,
    InfinityAdditionAlgebra318.X2,InfinityAdditionAlgebra318.Y2,MixedInputLocal318.finitePair,
    MixedFiniteInput318.finitePair_left,MixedFiniteInput318.finitePair_right]
  refine ⟨?_,?_,?_,?_⟩
  · rw [hu,←hx1]
    calc
      _=ψ (MixedFiniteInput318.firstFinite A B (MixedInputLocal318.finiteInput A B)
          (MixedInputLocal318.v_unit A B) (ShortAffineJacobian318.x A B))*
        (ψ (MixedFiniteInput318.firstFinite A B (MixedInputLocal318.finiteInput A B)
          (MixedInputLocal318.v_unit A B) (ShortAffineJacobian318.y A B))*
        ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.v A B))) := by ring
      _=_ := by rw [hy1,mul_one]
  · rw [hv,mul_comm]
    exact hy1
  · simpa only [MixedFiniteInput318.secondFinite,AlgHom.comp_apply,
      InfinityInputAlgebra318.x,InfinityInputAlgebra318.y] using hx
  · simpa only [MixedFiniteInput318.secondFinite,AlgHom.comp_apply,
      InfinityInputAlgebra318.y] using hy

theorem direct_agreement (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (φ:OutputRing A B →ₐ[R] S) (ψ:MixedInputLocal318.FiniteRing A B →ₐ[R] S)
    (hu:φ (u1 A B)=ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.u A B)))
    (hv:φ (v1 A B)=ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.v A B)))
    (hx:φ (u2 A B)*ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.y A B))=
      ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.x A B)))
    (hy:φ (v2 A B)*ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.y A B))=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ MixedInputLocal318.finiteAddition A B hD := by
  obtain ⟨h1,h2,h3,h4⟩:=finite_coordinates A B ψ (φ (u1 A B)) (φ (v1 A B))
    (φ (u2 A B)) (φ (v2 A B)) hu hv hx hy
  dsimp only [MixedInputLocal318.finiteAddition]
  rw [←Category.assoc,←Spec.map_comp]
  exact BothFiniteGlobalResolved318.scheme_agreement A B hD φ (ψ.comp (MixedInputLocal318.finitePair A B)) h1 h2 h3 h4

theorem reversed_agreement (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (φ:OutputRing A B →ₐ[R] S) (ψ:MixedInputLocal318.FiniteRing A B →ₐ[R] S)
    (hu:φ (u2 A B)=ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.u A B)))
    (hv:φ (v2 A B)=ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.v A B)))
    (hx:φ (u1 A B)*ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.y A B))=
      ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.x A B)))
    (hy:φ (v1 A B)*ψ (MixedInputLocal318.finiteInput A B (InfinityInputAlgebra318.y A B))=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ MixedInputLocal318.finiteAddition A B hD := by
  obtain ⟨h1,h2,h3,h4⟩:=finite_coordinates A B ψ (φ (u2 A B)) (φ (v2 A B))
    (φ (u1 A B)) (φ (v1 A B)) hu hv hx hy
  dsimp only [MixedInputLocal318.finiteAddition]
  rw [←Category.assoc,←Spec.map_comp]
  exact BothFiniteReversed318.scheme_agreement A B hD φ (ψ.comp (MixedInputLocal318.finitePair A B)) h1 h2 h3 h4

end BothMixedFiniteLocal318
