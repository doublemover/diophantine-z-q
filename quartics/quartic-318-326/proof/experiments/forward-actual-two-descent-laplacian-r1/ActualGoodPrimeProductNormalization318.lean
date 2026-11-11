module
public import ActualPrimitiveCorrectionProducts318
public section
noncomputable section
namespace ActualGoodPrimeProductNormalization318
open scoped BigOperators
open ActualGoodPrimeDensityProduct318 ActualPrimitiveCorrectionProducts318
open ActualLocalVolumeClosedForm318 ActualLocalPrimitiveNormalization318 ActualPrimitiveLocalVolume318
set_option maxHeartbeats 22000000

lemma actual_factorwise_normalization (κ : ℤ) (p : ℕ) :
    inversePowerFactor κ 4 p=factor κ p*inversePowerFactor κ 3 p := by
  classical
  unfold inversePowerFactor factor
  split_ifs with h
  · have hh := actual_primitive_normalization κ p h.1 h.2.1 h.2.2 0
    rw [actual_primitive_volume κ p h.1 h.2.1 h.2.2 0] at hh
    unfold ratio at hh
    exact_mod_cast hh
  · norm_num

/-- Exact identity of the genuine finite cutoff products. -/
theorem actual_finite_product_normalization (κ : ℤ) (S : Finset ℕ) :
    (∏p∈S,inversePowerFactor κ 4 p)=
      (∏p∈S,factor κ p)*(∏p∈S,inversePowerFactor κ 3 p) := by
  simp_rw [actual_factorwise_normalization]
  rw [Finset.prod_mul_distrib]

/-- The primitive global good-prime factor is the ACTUAL unrestricted
local-density product times the genuinely derived singular correction.
Both products are positive, so this identity does not hide zero products. -/
theorem actual_positive_product_normalization (κ : ℤ) :
    ∃S C P : ℝ,0<S ∧ 0<C ∧ 0<P ∧ HasProd (factor κ) S ∧
      HasProd (inversePowerFactor κ 3) C ∧ HasProd (inversePowerFactor κ 4) P ∧ P=S*C := by
  obtain ⟨S,hS,hprodS⟩ := actual_good_prime_positive_product κ
  obtain ⟨P,C,hP,hC,hprodP,hprodC⟩ := actual_primitive_and_correction_products κ
  have hh := hprodS.mul hprodC
  have he : (fun p => factor κ p*inversePowerFactor κ 3 p)=inversePowerFactor κ 4 := by
    funext p
    exact (actual_factorwise_normalization κ p).symm
  rw [he] at hh
  exact ⟨S,C,P,hS,hC,hP,hprodS,hprodC,hprodP,hprodP.unique hh⟩

end ActualGoodPrimeProductNormalization318
