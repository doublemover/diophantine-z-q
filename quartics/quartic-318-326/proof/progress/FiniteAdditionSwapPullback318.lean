module
public import FiniteAdditionCommutative318
public section
namespace FiniteAdditionSwapPullback318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
theorem equality (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f:RelativeChordAlgebra318.PairRing A B →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (f.comp (FinitePairSwap318.swap A B)).toRingHom) ≫
        FiniteAdditionGluing318.coordinateAddition A B hD=
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ FiniteAdditionGluing318.coordinateAddition A B hD := by
  have hh:=congrArg (fun k=>Spec.map (CommRingCat.ofHom f.toRingHom) ≫ k)
    (FiniteAdditionCommutative318.coordinate_commutative A B hD)
  rw [←Category.assoc,←Spec.map_comp] at hh
  exact hh
end FiniteAdditionSwapPullback318
