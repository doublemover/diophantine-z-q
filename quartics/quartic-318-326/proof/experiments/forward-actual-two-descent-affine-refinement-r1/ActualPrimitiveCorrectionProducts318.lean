module
public import ActualGoodPrimeDensityProduct318
public section
noncomputable section
namespace ActualPrimitiveCorrectionProducts318
open ActualGoodPrimeDensityProduct318
set_option maxHeartbeats 22000000

/-- The same EXACT good-prime set as the actual local density product. -/
@[expose] def inversePowerFactor (κ : ℤ) (s p : ℕ) : ℝ := by
  classical
  exact if Good κ p then 1-1/(p:ℝ)^s else 1
lemma inversePowerFactor_pos (κ : ℤ) (s p : ℕ) (hs : 1≤s) :
    0<inversePowerFactor κ s p := by
  classical
  unfold inversePowerFactor
  split_ifs with h
  · have hp1 : (1:ℝ)<p := by exact_mod_cast h.1.one_lt
    have hpow : (1:ℝ)<(p:ℝ)^s := one_lt_pow₀ hp1 (by omega)
    have hp0 : (0:ℝ)<(p:ℝ)^s := lt_trans (by norm_num) hpow
    have hh : (1:ℝ)/(p:ℝ)^s<1 := (div_lt_one hp0).mpr hpow
    linarith
  · norm_num
lemma inversePowerFactor_error (κ : ℤ) (s p : ℕ) :
    |inversePowerFactor κ s p-1|≤1/(p:ℝ)^s := by
  classical
  unfold inversePowerFactor
  split_ifs with h
  · have he : 1-1/(p:ℝ)^s-1= -(1/(p:ℝ)^s) := by ring
    rw [he,abs_neg,abs_of_nonneg (by positivity)]
  · simp only [sub_self,abs_zero]
    positivity

theorem actual_inverse_power_positive_product (κ : ℤ) (s : ℕ) (hs : 2≤s) :
    ∃C : ℝ,0<C ∧ HasProd (inversePowerFactor κ s) C := by
  have hsum : Summable (fun p : ℕ => 1/(p:ℝ)^s) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  have habs : Summable (fun p : ℕ => |inversePowerFactor κ s p-1|) :=
    hsum.of_nonneg_of_le (fun _ => abs_nonneg _) (inversePowerFactor_error κ s)
  exact positive_product_of_error _ (fun p => inversePowerFactor_pos κ s p (by omega)) habs

/-- Both the actual singular correction and primitive local product
are produced over the SAME original good-prime set. -/
theorem actual_primitive_and_correction_products (κ : ℤ) :
    ∃P C : ℝ,0<P ∧ 0<C ∧ HasProd (inversePowerFactor κ 4) P ∧
      HasProd (inversePowerFactor κ 3) C := by
  obtain ⟨P,hP,hprodP⟩ := actual_inverse_power_positive_product κ 4 (by norm_num)
  obtain ⟨C,hC,hprodC⟩ := actual_inverse_power_positive_product κ 3 (by norm_num)
  exact ⟨P,C,hP,hC,hprodP,hprodC⟩

end ActualPrimitiveCorrectionProducts318
