module
public import BothMixedWholeComparison318
public import BothInputSwap318
public section
noncomputable section
namespace BothExtractedComparison318
open BothInfinityAlgebra318 AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
theorem direct (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (φ:OutputRing A B →ₐ[R] S) (f:PairRing A B →ₐ[R] S)
    (h2:IsUnit (f (V2 A B))) (he:∀r, φ (pairMap A B r)=f r) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom (BothInputExtraction318.mixedPair A B f h2).toRingHom) ≫
        MixedAdditionGluing318.coordinateAddition A B hD := by
  apply BothMixedWholeComparison318.direct_agreement
  · rw [BothInputExtraction318.first_u]
    exact he _
  · rw [BothInputExtraction318.first_v]
    exact he _
  · change φ (pairMap A B (U2 A B))*_=_
    rw [he]
    exact BothInputExtraction318.second_x A B f h2
  · change φ (pairMap A B (V2 A B))*_=1
    rw [he]
    exact BothInputExtraction318.second_y A B f h2

theorem reversed (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (φ:OutputRing A B →ₐ[R] S) (f:PairRing A B →ₐ[R] S)
    (h1:IsUnit (f (V1 A B))) (he:∀r, φ (pairMap A B r)=f r) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom (BothInputSwap318.mixedLeft A B f h1).toRingHom) ≫
        MixedAdditionGluing318.coordinateAddition A B hD := by
  apply BothMixedWholeComparison318.reversed_agreement
  · rw [BothInputSwap318.mixedLeft_u]
    exact he _
  · rw [BothInputSwap318.mixedLeft_v]
    exact he _
  · change φ (pairMap A B (U1 A B))*_=_
    rw [he]
    exact BothInputSwap318.mixedLeft_x A B f h1
  · change φ (pairMap A B (V1 A B))*_=1
    rw [he]
    exact BothInputSwap318.mixedLeft_y A B f h1
end BothExtractedComparison318
