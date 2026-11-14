module
public import ActualOriginalFiveKernelCorrelation318
public section
noncomputable section
namespace ActualOriginalCompleteFiveKernel318
open QuadricCRTAssembly318 ActualOriginalFiniteBoxProduct318
open ActualOriginalWeightedWeylIdentity318 ActualOriginalCanonicalSupportBox318
open ActualOriginalDisplacementBoxKernel318
open scoped BigOperators

/-- All FIVE coordinates of the actual displacement set are covered
before the NONNEGATIVE majorant is factored. There are no lost outer
multiplicities and no factorization of the original weight. -/
theorem actual_complete_five_kernel (H : ℤ) (f₀ f₁ f₂ f₃ f₄ : ℤ → ℝ)
    (h₀ : ∀ a, 0≤f₀ a) (h₁ : ∀ a, 0≤f₁ a) (h₂ : ∀ a, 0≤f₂ a)
    (h₃ : ∀ a, 0≤f₃ a) (h₄ : ∀ a, 0≤f₄ a) :
    (∑ h∈differences (centeredBox H),
      f₀ h.1.1*f₁ h.1.2*f₂ h.2.1.1*f₃ h.2.1.2*f₄ h.2.2)≤
      (∑ a∈Finset.Icc (-2*H) (2*H), f₀ a)*
      (∑ a∈Finset.Icc (-2*H) (2*H), f₁ a)*
      (∑ a∈Finset.Icc (-2*H) (2*H), f₂ a)*
      (∑ a∈Finset.Icc (-2*H) (2*H), f₃ a)*
      (∑ a∈Finset.Icc (-2*H) (2*H), f₄ a) := by
  calc
    _ ≤ ∑ h∈centeredBox (2*H),
        f₀ h.1.1*f₁ h.1.2*f₂ h.2.1.1*f₃ h.2.1.2*f₄ h.2.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (actual_original_displacements_subset H)
        (fun h hh hn => mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (h₀ _) (h₁ _)) (h₂ _)) (h₃ _)) (h₄ _))
    _ = _ := by
      simp only [centeredBox,originalBox,Finset.sum_product,neg_mul]
      simp only [Finset.mul_sum,Finset.sum_mul]

end ActualOriginalCompleteFiveKernel318
