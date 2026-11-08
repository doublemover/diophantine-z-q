module
public import BothInputExtraction318
public import MixedAdditionExchange318
public section
noncomputable section
namespace BothInputSwap318
open BothInfinityAlgebra318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S T : Type u} [CommRing R] [CommRing S] [Algebra R S]
@[expose] def swap (A B:R) : PairRing A B →ₐ[R] PairRing A B :=
  (Algebra.TensorProduct.comm R (InfinityChart318.Ring A B) (InfinityChart318.Ring A B)).toAlgHom
@[simp] lemma swap_left (A B:R) (x:InfinityChart318.Ring A B) :
    swap A B (leftPair A B x)=rightPair A B x := by
  simp [swap,leftPair,rightPair,Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.comm_tmul]
@[simp] lemma swap_right (A B:R) (x:InfinityChart318.Ring A B) :
    swap A B (rightPair A B x)=leftPair A B x := by
  simp [swap,leftPair,rightPair,Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.comm_tmul]
@[simp] lemma swap_U1 (A B:R) : swap A B (U1 A B)=U2 A B := swap_left A B _
@[simp] lemma swap_V1 (A B:R) : swap A B (V1 A B)=V2 A B := swap_left A B _
@[simp] lemma swap_U2 (A B:R) : swap A B (U2 A B)=U1 A B := swap_right A B _
@[simp] lemma swap_V2 (A B:R) : swap A B (V2 A B)=V1 A B := swap_right A B _

@[expose] def mixedLeft (A B:R) (f:PairRing A B →ₐ[R] S) (h1:IsUnit (f (V1 A B))) :
    InfinityInputAlgebra318.PairRing A B →ₐ[R] S :=
  BothInputExtraction318.mixedPair A B (f.comp (swap A B))
    (by simpa only [AlgHom.comp_apply,swap_V2] using h1)
@[simp] lemma mixedLeft_u (A B:R) (f:PairRing A B →ₐ[R] S) (h1:IsUnit (f (V1 A B))) :
    mixedLeft A B f h1 (InfinityInputAlgebra318.u A B)=f (U2 A B) := by
  simp only [mixedLeft,BothInputExtraction318.first_u,AlgHom.comp_apply,swap_U1]
@[simp] lemma mixedLeft_v (A B:R) (f:PairRing A B →ₐ[R] S) (h1:IsUnit (f (V1 A B))) :
    mixedLeft A B f h1 (InfinityInputAlgebra318.v A B)=f (V2 A B) := by
  simp only [mixedLeft,BothInputExtraction318.first_v,AlgHom.comp_apply,swap_V1]
lemma mixedLeft_x (A B:R) (f:PairRing A B →ₐ[R] S) (h1:IsUnit (f (V1 A B))) :
    f (U1 A B)*mixedLeft A B f h1 (InfinityInputAlgebra318.y A B)=
      mixedLeft A B f h1 (InfinityInputAlgebra318.x A B) := by
  simpa only [mixedLeft,AlgHom.comp_apply,swap_U2] using
    BothInputExtraction318.second_x A B (f.comp (swap A B))
      (by simpa only [AlgHom.comp_apply,swap_V2] using h1)
lemma mixedLeft_y (A B:R) (f:PairRing A B →ₐ[R] S) (h1:IsUnit (f (V1 A B))) :
    f (V1 A B)*mixedLeft A B f h1 (InfinityInputAlgebra318.y A B)=1 := by
  simpa only [mixedLeft,AlgHom.comp_apply,swap_V2] using
    BothInputExtraction318.second_y A B (f.comp (swap A B))
      (by simpa only [AlgHom.comp_apply,swap_V2] using h1)

theorem mixedLeft_natural {T : Type u} [CommRing T] [Algebra R T]
    (A B:R) (f:PairRing A B →ₐ[R] S) (h1:IsUnit (f (V1 A B))) (g:S →ₐ[R] T) :
    g.comp (mixedLeft A B f h1)=mixedLeft A B (g.comp f) (h1.map g) := by
  unfold mixedLeft
  rw [BothInputExtraction318.mixedPair_natural]
  rfl

/-- Actual compatibility of the two whole mixed-input laws on the complete
finite-transition overlap in the infinity-times-infinity product. -/
theorem mixed_agreement (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f:PairRing A B →ₐ[R] S) (h1:IsUnit (f (V1 A B))) (h2:IsUnit (f (V2 A B))) :
    Spec.map (CommRingCat.ofHom (BothInputExtraction318.mixedPair A B f h2).toRingHom) ≫
        MixedAdditionGluing318.coordinateAddition A B hD=
      Spec.map (CommRingCat.ofHom (mixedLeft A B f h1).toRingHom) ≫
        MixedAdditionGluing318.coordinateAddition A B hD := by
  apply MixedAdditionExchange318.scheme_agreement
  · rw [BothInputExtraction318.first_u]
    exact mixedLeft_x A B f h1
  · rw [BothInputExtraction318.first_v]
    exact mixedLeft_y A B f h1
  · rw [mixedLeft_u]
    exact BothInputExtraction318.second_x A B f h2
  · rw [mixedLeft_v]
    exact BothInputExtraction318.second_y A B f h2
end BothInputSwap318
