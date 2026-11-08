module
public import BothFiniteRegular318
public import FiniteAdditionLocal318
public section
noncomputable section
namespace BothFiniteLocal318
open BothInfinityAlgebra318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The regular both-infinity law agrees with all four finite-input local Scheme
laws, under only the four literal input-coordinate transition equalities. -/
theorem scheme_agreement (A B:R) (i : Fin 4) (φ : OutputRing A B →ₐ[R] S)
    (ψ : FiniteAdditionLocal318.LocalRing A B i →ₐ[R] S)
    (hu : φ (u1 A B)*ψ (FiniteAdditionLocal318.inputMap A B i (InfinityAdditionAlgebra318.Y1 A B))=
      ψ (FiniteAdditionLocal318.inputMap A B i (InfinityAdditionAlgebra318.X1 A B)))
    (hv : φ (v1 A B)*ψ (FiniteAdditionLocal318.inputMap A B i (InfinityAdditionAlgebra318.Y1 A B))=1)
    (ht : φ (u2 A B)*ψ (FiniteAdditionLocal318.inputMap A B i (InfinityAdditionAlgebra318.Y2 A B))=
      ψ (FiniteAdditionLocal318.inputMap A B i (InfinityAdditionAlgebra318.X2 A B)))
    (hw : φ (v2 A B)*ψ (FiniteAdditionLocal318.inputMap A B i (InfinityAdditionAlgebra318.Y2 A B))=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ FiniteAdditionLocal318.localAddition A B i := by
  fin_cases i
  · change _=Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      (RelativeChordScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)
    exact BothFiniteRegular318.chord_agreement A B φ ψ hu hv ht hw
  · change _=Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      (TangentOpenScheme318.addition A B ≫ WeierstrassGluing318.finiteChart A B)
    exact BothFiniteRegular318.tangent_agreement A B φ ψ hu hv ht hw
  · exact BothFiniteInfinity318.scheme_agreement A B false φ ψ hu hv ht hw
  · exact BothFiniteInfinity318.scheme_agreement A B true φ ψ hu hv ht hw

end BothFiniteLocal318
