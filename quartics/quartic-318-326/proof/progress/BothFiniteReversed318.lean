module
public import BothFiniteGlobalResolved318
public import FiniteAdditionCommutative318
public import FiniteAdditionSwapPullback318
public section
noncomputable section
namespace BothFiniteReversed318
open BothInfinityAlgebra318 AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
theorem scheme_agreement (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (φ:OutputRing A B →ₐ[R] S) (f:RelativeChordAlgebra318.PairRing A B →ₐ[R] S)
    (hu:φ (u2 A B)*f (InfinityAdditionAlgebra318.Y1 A B)=f (InfinityAdditionAlgebra318.X1 A B))
    (hv:φ (v2 A B)*f (InfinityAdditionAlgebra318.Y1 A B)=1)
    (ht:φ (u1 A B)*f (InfinityAdditionAlgebra318.Y2 A B)=f (InfinityAdditionAlgebra318.X2 A B))
    (hw:φ (v1 A B)*f (InfinityAdditionAlgebra318.Y2 A B)=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ FiniteAdditionGluing318.coordinateAddition A B hD := by
  have hh:Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom (f.comp (FinitePairSwap318.swap A B)).toRingHom) ≫
        FiniteAdditionGluing318.coordinateAddition A B hD := by
    apply BothFiniteGlobalResolved318.scheme_agreement
    · simpa only [AlgHom.comp_apply,FinitePairSwap318.swap_X1,FinitePairSwap318.swap_Y1] using ht
    · simpa only [AlgHom.comp_apply,FinitePairSwap318.swap_Y1] using hw
    · simpa only [AlgHom.comp_apply,FinitePairSwap318.swap_X2,FinitePairSwap318.swap_Y2] using hu
    · simpa only [AlgHom.comp_apply,FinitePairSwap318.swap_Y2] using hv
  exact hh.trans (FiniteAdditionSwapPullback318.equality A B hD f)
end BothFiniteReversed318
