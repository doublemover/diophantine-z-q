module
public import ActualOriginalFlexibleMomentBudget318
public section
noncomputable section
namespace ActualOriginalFlexibleMinorBound318
open ActualOriginalPolynomialMinorScale318 QuadricCRTAssembly318 ActualOriginalFlexibleMinorScale318 ActualOriginalFlexibleKernelBudget318
open ActualOriginalFlexibleMomentBudget318 ActualOriginalIntegratedMinorMoment318
open ActualOriginalFiveQuadraticPrefixes318 ActualOriginalQuadraticEnergyCount318
open ActualOriginalCircleMinorArcIdentity318
open scoped ContDiff

/-- Explicit exponent audit: kernel sqrt n^(p*8+29), fourth moment n^(p*16+65),
actual full minor n^(p*24+94), versus the original B^3=n^(24p+96). -/
theorem actual_flexible_minor_bound (p : ℕ) (κ : ℤ) (hκ : κ≠0)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, 2≤n →
      ‖minorArcIntegral κ (minorCutoff n) (flexibleScale p n) W‖≤K*(n : ℝ)^(p*24+94) := by
  obtain ⟨R,C,hR,hC,hb⟩ := actual_original_integrated_minor_moment κ hκ W hW hc
  let D := flexibleKernelConstant p (-κ) (R+1)
  let E := flexibleMomentConstant p (R+1)
  let K := C*(2*R+3)^5*Real.sqrt D*E
  have hD : 0≤D := actual_flexible_kernel_nonneg p (-κ) (R+1) (by linarith)
  have hE : 0≤E := actual_flexible_moment_nonneg p (R+1)
  refine ⟨K,by dsimp [K]; positivity,fun n hn => ?_⟩
  obtain ⟨hN,hB,hs⟩ := actual_flexible_minor_scale p n hn
  have hδ : 0<(flexibleDivisorExponent p) := actual_flexible_exponent_pos p
  let H := canonicalMomentRadius R (flexibleScale p n)
  have hH : (H : ℝ)≤(R+1)*(n : ℝ)^(p*8+32) := actual_flexible_radius R hR p n hn
  have hk := actual_flexible_kernel_sqrt (-κ) p H n (R+1) hn (by linarith) hH
  have hm := actual_flexible_moment p H n (R+1) hn (by linarith) hH
  have hb' := hb (minorCutoff n) hN (flexibleScale p n) (flexibleDivisorExponent p) hB hs hδ
  simp only [originalPrefixIntegralBudget,actual_flexible_dirichlet_order p n (by omega)] at hb'
  have hp := mul_le_mul hk hm (actual_moment_budget_nonneg H (flexibleDivisorExponent p) hδ)
    (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcp : 0≤C*(2*R+3)^5 := by positivity
  apply hb'.trans
  apply (mul_le_mul_of_nonneg_left hp hcp).trans_eq
  dsimp only [K,D,E]
  simp only [pow_add,pow_mul]
  ring

/-- The exact ORIGINAL complex B^3 normalization, not a renamed
remainder. Every n>=2 has the quantitative K/n² estimate. -/
theorem actual_flexible_minor_normalized_bound (p : ℕ) (κ : ℤ) (hκ : κ≠0)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, 2≤n →
      ‖minorArcIntegral κ (minorCutoff n) (flexibleScale p n) W/(flexibleScale p n : ℂ)^3‖≤K/(n : ℝ)^2 := by
  obtain ⟨K,hK,hb⟩ := actual_flexible_minor_bound p κ hκ W hW hc
  refine ⟨K,hK,fun n hn => ?_⟩
  have hx : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hB0 : 0≤flexibleScale p n := pow_nonneg (Nat.cast_nonneg n) (p*8+32)
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB0]
  apply (div_le_div_of_nonneg_right (hb n hn) (pow_nonneg hB0 3)).trans_eq
  unfold flexibleScale
  field_simp [ne_of_gt hx]
  <;> simp only [pow_add,pow_mul] <;> ring

end ActualOriginalFlexibleMinorBound318
