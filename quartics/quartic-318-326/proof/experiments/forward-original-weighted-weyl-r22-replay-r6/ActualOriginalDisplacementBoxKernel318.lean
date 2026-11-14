module
public import ActualOriginalPlaneOuterMultiplicity318
public section
noncomputable section
namespace ActualOriginalDisplacementBoxKernel318
open QuadricCRTAssembly318 ActualOriginalFiniteBoxProduct318
open ActualOriginalWeightedWeylIdentity318 ActualOriginalCanonicalSupportBox318
open scoped BigOperators

lemma actual_interval_difference_mem (H x y : ℤ)
    (hx : x∈Finset.Icc (-H) H) (hy : y∈Finset.Icc (-H) H) :
    x-y∈Finset.Icc (-(2*H)) (2*H) := by
  have hx' := Finset.mem_Icc.mp hx
  have hy' := Finset.mem_Icc.mp hy
  apply Finset.mem_Icc.mpr
  omega

/-- Coverage of ALL five actual displacement coordinates. Enlargement
is a subset argument, not an assumed parametrization with lost fibers. -/
lemma actual_original_displacements_subset (H : ℤ) :
    differences (centeredBox H)⊆centeredBox (2*H) := by
  intro h hh
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
  simp only [centeredBox,originalBox,Finset.mem_product] at hx hy ⊢
  exact ⟨⟨actual_interval_difference_mem H _ _ hx.1.1 hy.1.1,
      actual_interval_difference_mem H _ _ hx.1.2 hy.1.2⟩,
    ⟨⟨actual_interval_difference_mem H _ _ hx.2.1.1 hy.2.1.1,
      actual_interval_difference_mem H _ _ hx.2.1.2 hy.2.1.2⟩,
      actual_interval_difference_mem H _ _ hx.2.2 hy.2.2⟩⟩

/-- Only a NONNEGATIVE KERNEL majorant is factored. The arbitrary
original weight was already controlled by its produced mixed variation.
The other THREE displacement multiplicities remain as an explicit cube. -/
theorem actual_complete_two_axis_kernel (H : ℤ) (hH : 0≤H) (f g : ℤ → ℝ)
    (hf : ∀ a, 0≤f a) (hg : ∀ b, 0≤g b) :
    (∑ h∈differences (centeredBox H), f h.1.1*g h.1.2)≤
      (4*(H : ℝ)+1)^3*(∑ a∈Finset.Icc (-2*H) (2*H), f a)*
        (∑ b∈Finset.Icc (-2*H) (2*H), g b) := by
  have hcard : ((Finset.Icc (-(2*H)) (2*H)).card : ℝ)=4*(H : ℝ)+1 := by
    rw [Int.card_Icc]
    have hi : (2*H+1-(-(2*H))).toNat=(4*H+1).toNat := by congr 1; ring
    rw [hi]
    have hn : (0 : ℤ)≤4*H+1 := by omega
    exact_mod_cast Int.toNat_of_nonneg hn
  calc
    _ ≤ ∑ h∈centeredBox (2*H), f h.1.1*g h.1.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (actual_original_displacements_subset H)
        (fun h hh hn => mul_nonneg (hf _) (hg _))
    _ = _ := by
      simp only [centeredBox,originalBox,Finset.sum_product,
        Finset.sum_const,nsmul_eq_mul,hcard,neg_mul]
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

end ActualOriginalDisplacementBoxKernel318
