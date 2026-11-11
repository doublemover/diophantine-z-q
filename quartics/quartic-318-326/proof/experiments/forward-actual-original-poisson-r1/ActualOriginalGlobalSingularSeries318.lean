module
public import ActualOriginalGlobalSeriesSummable318
public section
noncomputable section
namespace ActualOriginalGlobalSingularSeries318
open ActualOriginalGlobalCoefficient318 ActualOriginalGlobalSeriesSummable318
open ActualOriginalUnitLocalSeries318 ActualOriginalAllPrimeFactors318
open ActualOriginalNonarchimedeanProduct318
open scoped BigOperators
set_option maxHeartbeats 16000000

lemma actual318_complex_euler_factor (p : ℕ) :
    Set.mulIndicator {p : ℕ | p.Prime} (fun p => ∑' n, coefficient 318 (p^n)) p =
      (density318 p : ℂ) := by
  classical
  by_cases hp : p.Prime
  · letI : NeZero p := ⟨hp.ne_zero⟩
    rw [Set.mulIndicator_of_mem hp]
    simp_rw [actual_coefficient_nonzero]
    exact (actual318_unit_local_series p hp).2.tsum_eq
  · rw [Set.mulIndicator_of_notMem hp]
    simp only [density318,if_neg hp,Complex.ofReal_one]

lemma actual326_complex_euler_factor (p : ℕ) :
    Set.mulIndicator {p : ℕ | p.Prime} (fun p => ∑' n, coefficient 326 (p^n)) p =
      (density326 p : ℂ) := by
  classical
  by_cases hp : p.Prime
  · letI : NeZero p := ⟨hp.ne_zero⟩
    rw [Set.mulIndicator_of_mem hp]
    simp_rw [actual_coefficient_nonzero]
    exact (actual326_unit_local_series p hp).2.tsum_eq
  · rw [Set.mulIndicator_of_notMem hp]
    simp only [density326,if_neg hp,Complex.ofReal_one]

/-- The SINGLE global denominator series is absolutely convergent and
sums to the strictly positive full original local-density Euler product.
Every coefficient is the literal q^-5 unit-frequency character sum; no
primitive-point scaling factor or surrogate local series is substituted. -/
theorem actual318_global_singular_series :
    ∃ S : ℝ, 0<S ∧ HasSum (coefficient 318) (S : ℂ) ∧ HasProd density318 S := by
  obtain ⟨S,hS,hprod⟩ := actual_full318_positive_product
  have he := EulerProduct.eulerProduct_hasProd_mulIndicator
    (actual_coefficient_one 318) (actual_coefficient_coprime 318)
    actual318_global_norm_summable (actual_coefficient_zero 318)
  have hfac := funext actual318_complex_euler_factor
  rw [hfac] at he
  have hc : HasProd (fun p => (density318 p : ℂ)) (S : ℂ) :=
    hprod.map Complex.ofRealHom Complex.continuous_ofReal
  have hv : (∑' q, coefficient 318 q) = (S : ℂ) := he.unique hc
  refine ⟨S,hS,?_,hprod⟩
  simpa only [hv] using actual318_global_norm_summable.of_norm.hasSum

theorem actual326_global_singular_series :
    ∃ S : ℝ, 0<S ∧ HasSum (coefficient 326) (S : ℂ) ∧ HasProd density326 S := by
  obtain ⟨S,hS,hprod⟩ := actual_full326_positive_product
  have he := EulerProduct.eulerProduct_hasProd_mulIndicator
    (actual_coefficient_one 326) (actual_coefficient_coprime 326)
    actual326_global_norm_summable (actual_coefficient_zero 326)
  have hfac := funext actual326_complex_euler_factor
  rw [hfac] at he
  have hc : HasProd (fun p => (density326 p : ℂ)) (S : ℂ) :=
    hprod.map Complex.ofRealHom Complex.continuous_ofReal
  have hv : (∑' q, coefficient 326 q) = (S : ℂ) := he.unique hc
  refine ⟨S,hS,?_,hprod⟩
  simpa only [hv] using actual326_global_norm_summable.of_norm.hasSum

end ActualOriginalGlobalSingularSeries318
