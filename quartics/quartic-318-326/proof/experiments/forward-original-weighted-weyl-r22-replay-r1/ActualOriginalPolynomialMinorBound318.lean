module
public import ActualOriginalPolynomialMomentBudget318
public section
noncomputable section
namespace ActualOriginalPolynomialMinorBound318
open QuadricCRTAssembly318 ActualOriginalPolynomialMinorScale318 ActualOriginalPolynomialKernelBudget318
open ActualOriginalPolynomialMomentBudget318 ActualOriginalIntegratedMinorMoment318
open ActualOriginalFiveQuadraticPrefixes318 ActualOriginalQuadraticEnergyCount318
open ActualOriginalCircleMinorArcIdentity318
open scoped ContDiff

/-- Explicit exponent audit: kernel sqrt n^29, fourth moment n^65,
actual full minor n^94, versus the original B^3=n^96. -/
theorem actual_polynomial_minor_bound (κ : ℤ) (hκ : κ≠0)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, 2≤n →
      ‖minorArcIntegral κ (minorCutoff n) (minorScale n) W‖≤K*(n : ℝ)^94 := by
  obtain ⟨R,C,hR,hC,hb⟩ := actual_original_integrated_minor_moment κ hκ W hW hc
  let D := kernelPolynomialConstant (-κ) (R+1)
  let E := momentPolynomialConstant (R+1)
  let K := C*(2*R+3)^5*Real.sqrt D*E
  have hD : 0≤D := actual_kernel_polynomial_nonneg (-κ) (R+1) (by linarith)
  have hE : 0≤E := actual_moment_polynomial_nonneg (R+1)
  refine ⟨K,by dsimp [K]; positivity,fun n hn => ?_⟩
  obtain ⟨hN,hB,hs⟩ := actual_polynomial_minor_scale n hn
  have hδ : 0<minorDivisorExponent := by norm_num [minorDivisorExponent]
  let H := canonicalMomentRadius R (minorScale n)
  have hH : (H : ℝ)≤(R+1)*(n : ℝ)^32 := actual_polynomial_radius R hR n hn
  have hk := actual_polynomial_kernel_sqrt (-κ) H n (R+1) hn (by linarith) hH
  have hm := actual_polynomial_moment H n (R+1) hn (by linarith) hH
  have hb' := hb (minorCutoff n) hN (minorScale n) minorDivisorExponent hB hs hδ
  simp only [originalPrefixIntegralBudget,actual_polynomial_dirichlet_order n (by omega)] at hb'
  have hp := mul_le_mul hk hm (actual_moment_budget_nonneg H minorDivisorExponent hδ)
    (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcp : 0≤C*(2*R+3)^5 := by positivity
  apply hb'.trans
  apply (mul_le_mul_of_nonneg_left hp hcp).trans_eq
  dsimp only [K,D,E]
  ring

/-- The exact ORIGINAL complex B^3 normalization, not a renamed
remainder. Every n>=2 has the quantitative K/n² estimate. -/
theorem actual_polynomial_minor_normalized_bound (κ : ℤ) (hκ : κ≠0)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, 2≤n →
      ‖minorArcIntegral κ (minorCutoff n) (minorScale n) W/(minorScale n : ℂ)^3‖≤K/(n : ℝ)^2 := by
  obtain ⟨K,hK,hb⟩ := actual_polynomial_minor_bound κ hκ W hW hc
  refine ⟨K,hK,fun n hn => ?_⟩
  have hx : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hB0 : 0≤minorScale n := pow_nonneg (Nat.cast_nonneg n) 32
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB0]
  apply (div_le_div_of_nonneg_right (hb n hn) (pow_nonneg hB0 3)).trans_eq
  unfold minorScale
  field_simp [ne_of_gt hx]
  <;> ring

end ActualOriginalPolynomialMinorBound318
