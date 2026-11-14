module
public import ActualOriginalMixedAbelBound318
public section
noncomputable section
namespace ActualOriginalMixedVariationBudget318
open ActualOriginalFiniteAbel318 ActualOriginalMixedAbelIdentity318
open scoped BigOperators

/-- The mixed variation uses the corner, BOTH boundary first differences,
and EVERY interior mixed difference. No interior term is replaced by two
independent first-variation assumptions. -/
theorem actual_mixed_variation_budget (g : ℕ → ℕ → ℂ) (N M : ℕ)
    (A D₀ D₁ D₀₁ : ℝ) (hc : ‖g N M‖≤A)
    (h₀ : ∀ i∈Finset.range N, ‖g i M-g (i+1) M‖≤D₀)
    (h₁ : ∀ j∈Finset.range M, ‖g N j-g N (j+1)‖≤D₁)
    (h₀₁ : ∀ i∈Finset.range N, ∀ j∈Finset.range M,
      ‖(g i j-g i (j+1))-(g (i+1) j-g (i+1) (j+1))‖≤D₀₁) :
    mixedVariation g N M≤A+(N : ℝ)*D₀+(M : ℝ)*D₁+(N : ℝ)*(M : ℝ)*D₀₁ := by
  have hb₀ : variation (fun i => g i M) N≤A+(N : ℝ)*D₀ := by
    unfold variation
    apply add_le_add hc
    calc
      _ ≤ ∑ i∈Finset.range N, D₀ := Finset.sum_le_sum h₀
      _ = _ := by simp [nsmul_eq_mul]
  have hb₁ (j : ℕ) (hj : j∈Finset.range M) :
      variation (fun i => g i j-g i (j+1)) N≤D₁+(N : ℝ)*D₀₁ := by
    unfold variation
    apply add_le_add (h₁ j hj)
    calc
      _ ≤ ∑ i∈Finset.range N, D₀₁ := Finset.sum_le_sum (fun i hi => h₀₁ i hi j hj)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ ≤ (A+(N : ℝ)*D₀)+∑ j∈Finset.range M, (D₁+(N : ℝ)*D₀₁) :=
      add_le_add hb₀ (Finset.sum_le_sum hb₁)
    _ = _ := by simp [nsmul_eq_mul]; ring

/-- Scale-uniform mixed control follows from first increments of size1/B
and genuine mixed increments of size1/B² on O(B)-by-O(B) rectangles.
The mixed-increment premise remains explicit until analytically produced. -/
theorem actual_scaled_mixed_variation_budget (g : ℕ → ℕ → ℂ) (N M : ℕ)
    (B R A D₀ D₁ D₀₁ : ℝ) (hB : 0<B) (hR : 0≤R)
    (hD₀ : 0≤D₀) (hD₁ : 0≤D₁) (hD₀₁ : 0≤D₀₁)
    (hN : (N : ℝ)≤R*B) (hM : (M : ℝ)≤R*B)
    (hc : ‖g N M‖≤A)
    (h₀ : ∀ i∈Finset.range N, ‖g i M-g (i+1) M‖≤D₀/B)
    (h₁ : ∀ j∈Finset.range M, ‖g N j-g N (j+1)‖≤D₁/B)
    (h₀₁ : ∀ i∈Finset.range N, ∀ j∈Finset.range M,
      ‖(g i j-g i (j+1))-(g (i+1) j-g (i+1) (j+1))‖≤D₀₁/B^2) :
    mixedVariation g N M≤A+R*D₀+R*D₁+R^2*D₀₁ := by
  apply (actual_mixed_variation_budget g N M A (D₀/B) (D₁/B) (D₀₁/B^2) hc h₀ h₁ h₀₁).trans
  have h0 := mul_le_mul_of_nonneg_right hN (div_nonneg hD₀ (le_of_lt hB))
  have h1 := mul_le_mul_of_nonneg_right hM (div_nonneg hD₁ (le_of_lt hB))
  have hprod := mul_le_mul hN hM (Nat.cast_nonneg M) (mul_nonneg hR (le_of_lt hB))
  have h01 := mul_le_mul_of_nonneg_right hprod (div_nonneg hD₀₁ (sq_nonneg B))
  have hBn : B≠0 := ne_of_gt hB
  have e0 : (R*B)*(D₀/B)=R*D₀ := by field_simp [hBn]; ring
  have e1 : (R*B)*(D₁/B)=R*D₁ := by field_simp [hBn]; ring
  have e01 : (R*B)*(R*B)*(D₀₁/B^2)=R^2*D₀₁ := by field_simp [hBn]; ring
  rw [e0] at h0
  rw [e1] at h1
  rw [e01] at h01
  linarith

end ActualOriginalMixedVariationBudget318
