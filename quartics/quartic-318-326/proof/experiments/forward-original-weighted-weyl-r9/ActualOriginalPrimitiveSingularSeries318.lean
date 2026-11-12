module
public import ActualAllPrimePrimitiveDensity318
public section
noncomputable section
namespace ActualOriginalPrimitiveSingularSeries318
open Filter ActualOriginalAllPrimeFactors318 ActualOriginalNonarchimedeanProduct318
open ActualAllPrimePrimitiveDensity318 ActualGoodPrimeDensityProduct318 ActualOriginalLocalProductBounds318
open scoped Topology
set_option maxHeartbeats 28000000

@[expose] def primeCorrection (p : ℕ) : ℝ := if p.Prime then 1-1/(p:ℝ)^3 else 1
lemma primeCorrection_pos (p : ℕ) : 0<primeCorrection p := by
  unfold primeCorrection
  split_ifs with hp
  · have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
    have hpow : (1:ℝ)<(p:ℝ)^3 := one_lt_pow₀ hp1 (by norm_num)
    have hh := (div_lt_one (lt_trans (by norm_num) hpow)).mpr hpow
    linarith
  · norm_num
lemma primeCorrection_error (p : ℕ) : |primeCorrection p-1|≤1/(p:ℝ)^3 := by
  unfold primeCorrection
  split_ifs with hp
  · have he : 1-1/(p:ℝ)^3-1= -(1/(p:ℝ)^3) := by ring
    rw [he,abs_neg,abs_of_nonneg (by positivity)]
  · simp only [sub_self,abs_zero]
    positivity
lemma actual_all_prime_correction_product :
    ∃C : ℝ,0<C ∧ HasProd primeCorrection C := by
  have hs : Summable (fun p : ℕ => 1/(p:ℝ)^3) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  exact positive_product_of_error primeCorrection primeCorrection_pos
    (hs.of_nonneg_of_le (fun _ => abs_nonneg _) primeCorrection_error)

@[expose] def primitive318 (p : ℕ) : ℝ := density318 p*primeCorrection p
@[expose] def primitive326 (p : ℕ) : ℝ := density326 p*primeCorrection p

theorem actual_primitive318_every_prime (p : ℕ) (hp : p.Prime) :
    Tendsto (fun n : ℕ => (primitiveNormalized 318 p n:ℝ)) atTop (𝓝 (primitive318 p)) := by
  simpa only [primitive318,primeCorrection,if_pos hp] using
    actual_primitive_limit_of_whole 318 p hp (density318 p) (actual_318_every_prime p hp)
theorem actual_primitive326_every_prime (p : ℕ) (hp : p.Prime) :
    Tendsto (fun n : ℕ => (primitiveNormalized 326 p n:ℝ)) atTop (𝓝 (primitive326 p)) := by
  simpa only [primitive326,primeCorrection,if_pos hp] using
    actual_primitive_limit_of_whole 326 p hp (density326 p) (actual_326_every_prime p hp)

/-- Positive primitive singular-series factors for BOTH original
quartics, with every finite place actually supplied. These are NOT yet
an integer-point asymptotic or a global rational/prime witness. -/
theorem actual_both_primitive_positive_products :
    ∃P318 P326 : ℝ,0<P318 ∧ 0<P326 ∧ HasProd primitive318 P318 ∧ HasProd primitive326 P326 := by
  obtain ⟨S318,h318,hs318⟩ := actual_full318_positive_product
  obtain ⟨S326,h326,hs326⟩ := actual_full326_positive_product
  obtain ⟨C,hC,hprod⟩ := actual_all_prime_correction_product
  exact ⟨S318*C,S326*C,mul_pos h318 hC,mul_pos h326 hC,hs318.mul hprod,hs326.mul hprod⟩

theorem actual_primitive318_all_cutoffs :
    ∃L U : ℝ,0<L ∧ 0<U ∧ ∀N,L≤partialProduct primitive318 N ∧ partialProduct primitive318 N≤U := by
  obtain ⟨P,Q,hP,hQ,hprod,hprodQ⟩ := actual_both_primitive_positive_products
  exact all_cutoff_bounds primitive318 (fun p => mul_pos (density318_pos p) (primeCorrection_pos p)) P hP hprod
theorem actual_primitive326_all_cutoffs :
    ∃L U : ℝ,0<L ∧ 0<U ∧ ∀N,L≤partialProduct primitive326 N ∧ partialProduct primitive326 N≤U := by
  obtain ⟨P,Q,hP,hQ,hprodP,hprod⟩ := actual_both_primitive_positive_products
  exact all_cutoff_bounds primitive326 (fun p => mul_pos (density326_pos p) (primeCorrection_pos p)) Q hQ hprod

end ActualOriginalPrimitiveSingularSeries318
