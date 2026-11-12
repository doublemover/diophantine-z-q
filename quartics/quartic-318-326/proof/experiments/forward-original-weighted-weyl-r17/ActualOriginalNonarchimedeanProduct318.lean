module
public import ActualOriginalExceptionalProducts318
public section
noncomputable section
namespace ActualOriginalNonarchimedeanProduct318
open scoped BigOperators Topology
open Filter ActualOriginalAllPrimeFactors318 ActualOriginalExceptionalProducts318
open ActualGoodPrimeDensityProduct318 ActualOriginalLocalProductBounds318
set_option maxHeartbeats 24000000

lemma density318_pos (p : ℕ) : 0<density318 p := by
  rw [actual_318_factorization]
  exact mul_pos (factor_pos 318 p) (exceptional318_pos p)
lemma density326_pos (p : ℕ) : 0<density326 p := by
  rw [actual_326_factorization]
  exact mul_pos (factor_pos 326 p) (exceptional326_pos p)

/-- The ENTIRE finite-prime factor of the original318 quadric is a
constructed strictly positive product of its actual local-count limits. -/
theorem actual_full318_positive_product : ∃S : ℝ,0<S ∧ HasProd density318 S := by
  obtain ⟨G,hG,hprod⟩ := actual_good_prime_positive_product 318
  refine ⟨G*((8/7)*(16/13)*(2916/2863)),mul_pos hG (by norm_num),?_⟩
  have hh := hprod.mul actual_exceptional318_product
  have he : (fun p => factor 318 p*exceptional318 p)=density318 := by
    funext p
    exact (actual_318_factorization p).symm
  rw [he] at hh
  exact hh

theorem actual_full326_positive_product : ∃S : ℝ,0<S ∧ HasProd density326 S := by
  obtain ⟨G,hG,hprod⟩ := actual_good_prime_positive_product 326
  refine ⟨G*((8/7)*(26896/26733)),mul_pos hG (by norm_num),?_⟩
  have hh := hprod.mul actual_exceptional326_product
  have he : (fun p => factor 326 p*exceptional326 p)=density326 := by
    funext p
    exact (actual_326_factorization p).symm
  rw [he] at hh
  exact hh

/-- No small cutoff, including cutoffs before a bad prime appears,
is discarded in the assembled original local-product control. -/
theorem actual_full318_all_cutoffs :
    ∃L U : ℝ,0<L ∧ 0<U ∧ ∀N,L≤partialProduct density318 N ∧ partialProduct density318 N≤U := by
  obtain ⟨S,hS,hprod⟩ := actual_full318_positive_product
  exact all_cutoff_bounds density318 density318_pos S hS hprod

theorem actual_full326_all_cutoffs :
    ∃L U : ℝ,0<L ∧ 0<U ∧ ∀N,L≤partialProduct density326 N ∧ partialProduct density326 N≤U := by
  obtain ⟨S,hS,hprod⟩ := actual_full326_positive_product
  exact all_cutoff_bounds density326 density326_pos S hS hprod

end ActualOriginalNonarchimedeanProduct318
