module
public import ActualTwoDescentInfinityEisenstein318
public section
noncomputable section
namespace ActualTwoDescentInfinitySwapEquivalence318
open Polynomial ActualTwoDescentInfinityChartRing318
open ActualTwoDescentInfinitySwappedCubic318 ActualTwoDescentInfinityEisenstein318
variable {K : Type*} [Field K] [CharZero K]

def swapToOriginal (n : K) : SwappedChart n →+* InfinityChart n :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (chartCoefficient n) (chartV n)) (chartU n) (by
    have h := actual_chart_cubic_relation n
    unfold chartFactor at h
    simp only [map_mul,map_pow,map_ofNat] at h
    simp [swappedPolynomial,Cubic.toPoly]
    linear_combination -h)

def originalToSwap (n : K) : InfinityChart n →+* SwappedChart n :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (swappedCoefficient n) (swappedU n)) (swappedV n) (by
    have h := actual_swapped_relation n
    simp only [map_mul,map_pow,map_ofNat] at h
    simp [infinityPolynomial]
    linear_combination -h)

@[simp] lemma actual_swap_u (n : K) : swapToOriginal n (swappedU n)=chartU n := by
  simp [swapToOriginal,swappedU]
@[simp] lemma actual_swap_v (n : K) : swapToOriginal n (swappedV n)=chartV n := by
  simp [swapToOriginal,swappedV]
@[simp] lemma actual_swap_coefficient (n a : K) :
    swapToOriginal n (swappedCoefficient n a)=chartCoefficient n a := by
  simp [swapToOriginal,swappedCoefficient]
@[simp] lemma actual_original_to_swap_u (n : K) : originalToSwap n (chartU n)=swappedU n := by
  simp [originalToSwap,chartU]
@[simp] lemma actual_original_to_swap_v (n : K) : originalToSwap n (chartV n)=swappedV n := by
  simp [originalToSwap,chartV]
@[simp] lemma actual_original_to_swap_coefficient (n a : K) :
    originalToSwap n (chartCoefficient n a)=swappedCoefficient n a := by
  simp [originalToSwap,chartCoefficient]

lemma actual_swap_left_inverse (n : K) :
    (originalToSwap n).comp (swapToOriginal n)=RingHom.id (SwappedChart n) := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · ext a
      change originalToSwap n (swapToOriginal n (swappedCoefficient n a))=swappedCoefficient n a
      simp
    · change originalToSwap n (swapToOriginal n (swappedV n))=swappedV n
      simp
  · change originalToSwap n (swapToOriginal n (swappedU n))=swappedU n
    simp

lemma actual_swap_right_inverse (n : K) :
    (swapToOriginal n).comp (originalToSwap n)=RingHom.id (InfinityChart n) := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · ext a
      change swapToOriginal n (originalToSwap n (chartCoefficient n a))=chartCoefficient n a
      simp
    · change swapToOriginal n (originalToSwap n (chartU n))=chartU n
      simp
  · change swapToOriginal n (originalToSwap n (chartV n))=chartV n
    simp

/-- The native original quotient is explicitly isomorphic to the actual
Eisenstein quotient; no integral-domain structure is assumed on the source. -/
def infinitySwapEquiv (n : K) : SwappedChart n ≃+* InfinityChart n where
  toFun := swapToOriginal n
  invFun := originalToSwap n
  left_inv x := DFunLike.congr_fun (actual_swap_left_inverse n) x
  right_inv x := DFunLike.congr_fun (actual_swap_right_inverse n) x
  map_mul' := (swapToOriginal n).map_mul
  map_add' := (swapToOriginal n).map_add

end ActualTwoDescentInfinitySwapEquivalence318
