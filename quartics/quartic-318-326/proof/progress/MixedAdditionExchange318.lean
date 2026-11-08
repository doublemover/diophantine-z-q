module
public import MixedAdditionNaturality318
public import FiniteAdditionCommutative318
public import FiniteAdditionSwapPullback318
public import GenericCategoryInvariant318
public section
noncomputable section
namespace MixedAdditionExchange318
open AlgebraicGeometry CategoryTheory
open InfinityInputAlgebra318
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

theorem finitePair_swap (A B:R) (f g:PairRing A B →ₐ[R] S)
    (hvf:IsUnit (f (v A B))) (hvg:IsUnit (g (v A B)))
    (hx:f (u A B)*g (y A B)=g (x A B)) (hy:f (v A B)*g (y A B)=1)
    (ht:g (u A B)*f (y A B)=f (x A B)) (hw:g (v A B)*f (y A B)=1) :
    MixedFiniteInput318.finitePair A B f hvf=
      (MixedFiniteInput318.finitePair A B g hvg).comp (FinitePairSwap318.swap A B) := by
  have hfirst:MixedFiniteInput318.firstFinite A B f hvf=MixedFiniteInput318.secondFinite A B g := by
    symm
    apply MixedFiniteInput318.firstFinite_unique
    · change g (x A B)*f (v A B)=f (u A B)
      rw [←hx]
      calc
        _=f (u A B)*(f (v A B)*g (y A B)) := by ring
        _=_ := by rw [hy,mul_one]
    · change g (y A B)*f (v A B)=1
      rw [mul_comm]
      exact hy
  have hsecond:MixedFiniteInput318.firstFinite A B g hvg=MixedFiniteInput318.secondFinite A B f := by
    symm
    apply MixedFiniteInput318.firstFinite_unique
    · change f (x A B)*g (v A B)=g (u A B)
      rw [←ht]
      calc
        _=g (u A B)*(g (v A B)*f (y A B)) := by ring
        _=_ := by rw [hw,mul_one]
    · change f (y A B)*g (v A B)=1
      rw [mul_comm]
      exact hw
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro r
    change MixedFiniteInput318.finitePair A B f hvf (RelativeChordAlgebra318.leftPair A B r)=
      MixedFiniteInput318.finitePair A B g hvg (FinitePairSwap318.swap A B (RelativeChordAlgebra318.leftPair A B r))
    rw [MixedFiniteInput318.finitePair_left,FinitePairSwap318.swap_left,MixedFiniteInput318.finitePair_right]
    exact DFunLike.congr_fun hfirst r
  · apply AlgHom.ext
    intro r
    change MixedFiniteInput318.finitePair A B f hvf (RelativeChordAlgebra318.rightPair A B r)=
      MixedFiniteInput318.finitePair A B g hvg (FinitePairSwap318.swap A B (RelativeChordAlgebra318.rightPair A B r))
    rw [MixedFiniteInput318.finitePair_right,FinitePairSwap318.swap_right,MixedFiniteInput318.finitePair_left]
    exact (DFunLike.congr_fun hsecond r).symm

/-- The extracted finite input maps are related by the actual tensor exchange
on affine spectra, before any glued output morphism is substituted. -/
theorem finite_spec_swap (A B:R) (f g:PairRing A B →ₐ[R] S)
    (hvf:IsUnit (f (v A B))) (hvg:IsUnit (g (v A B)))
    (hx:f (u A B)*g (y A B)=g (x A B)) (hy:f (v A B)*g (y A B)=1)
    (ht:g (u A B)*f (y A B)=f (x A B)) (hw:g (v A B)*f (y A B)=1) :
    Spec.map (CommRingCat.ofHom (R:=RelativeChordAlgebra318.PairRing A B) (S:=S) (MixedFiniteInput318.finitePair A B f hvf).toRingHom)=
      Spec.map (CommRingCat.ofHom (R:=RelativeChordAlgebra318.PairRing A B) (S:=S) (MixedFiniteInput318.finitePair A B g hvg).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (R:=RelativeChordAlgebra318.PairRing A B) (S:=RelativeChordAlgebra318.PairRing A B) (FinitePairSwap318.swap A B).toRingHom) := by
  rw [finitePair_swap A B f g hvf hvg hx hy ht hw]
  exact Spec.map_comp (CommRingCat.ofHom (R:=RelativeChordAlgebra318.PairRing A B) (S:=RelativeChordAlgebra318.PairRing A B) (FinitePairSwap318.swap A B).toRingHom)
    (CommRingCat.ofHom (R:=RelativeChordAlgebra318.PairRing A B) (S:=S) (MixedFiniteInput318.finitePair A B g hvg).toRingHom)

/-- The two whole mixed laws agree when their two inputs are exchanged through
the literal finite/infinity chart transitions. This includes nonreduced algebras. -/
@[expose] def scheme_agreement (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f g:PairRing A B →ₐ[R] S)
    (hx:f (u A B)*g (y A B)=g (x A B)) (hy:f (v A B)*g (y A B)=1)
    (ht:g (u A B)*f (y A B)=f (x A B)) (hw:g (v A B)*f (y A B)=1) :=
  let hvf:IsUnit (f (v A B)):=IsUnit.of_mul_eq_one (g (y A B)) hy
  let hvg:IsUnit (g (v A B)):=IsUnit.of_mul_eq_one (f (y A B)) hw
  (MixedAdditionNaturality318.finite_restriction A B hD f hvf).trans
    ((GenericCategoryInvariant318.comparison
      (finite_spec_swap A B f g hvf hvg hx hy ht hw)
      (FiniteAdditionCommutative318.coordinate_commutative A B hD)).trans
      (MixedAdditionNaturality318.finite_restriction A B hD g hvg).symm)
end MixedAdditionExchange318
