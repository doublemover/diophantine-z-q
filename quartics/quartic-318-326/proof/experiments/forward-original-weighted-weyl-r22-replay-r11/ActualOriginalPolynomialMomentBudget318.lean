module
public import ActualOriginalPolynomialKernelBudget318
public section
noncomputable section
namespace ActualOriginalPolynomialMomentBudget318
open ActualOriginalPolynomialMinorScale318 ActualOriginalQuadraticEnergyCount318
open ActualDivisorSubpower318

@[expose] def momentPolynomialConstant (A : ℝ) : ℝ :=
  (2*A+1)^2*(2*divisorConstant minorDivisorExponent*(A^2)^minorDivisorExponent+4)

lemma actual_moment_polynomial_nonneg (A : ℝ) : 0≤momentPolynomialConstant A := by
  have hh := divisorConstant_pos minorDivisorExponent (by norm_num [minorDivisorExponent])
  unfold momentPolynomialConstant
  positivity

/-- Fixed delta=1/64, not a scale-varying divisor exponent. The exact
identity (n^64)^(1/64)=n yields a fourth-moment cost O(n^65). -/
theorem actual_polynomial_moment (H n : ℕ) (A : ℝ) (hn : 2≤n)
    (hA : 0≤A) (hH : (H : ℝ)≤A*(n : ℝ)^32) :
    momentBudget H minorDivisorExponent≤momentPolynomialConstant A*(n : ℝ)^65 := by
  have hx1 : (1 : ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hx0 : (0 : ℝ)≤n := by positivity
  have hδ : 0<minorDivisorExponent := by norm_num [minorDivisorExponent]
  have hC := divisorConstant_pos minorDivisorExponent hδ
  have hx32 : (1 : ℝ)≤(n : ℝ)^32 := one_le_pow₀ hx1
  have hL : 2*(H : ℝ)+1≤(2*A+1)*(n : ℝ)^32 := by nlinarith
  have hL2 : (2*(H : ℝ)+1)^2≤(2*A+1)^2*(n : ℝ)^64 := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤2*(H : ℝ)+1) hL 2
    convert hh using 1 <;> ring
  have hH2 : (H : ℝ)^2≤A^2*(n : ℝ)^64 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg H : (0 : ℝ)≤H) hH 2
    convert hh using 1 <;> ring
  have he : ((n : ℝ)^64)^minorDivisorExponent=(n : ℝ) := by
    rw [←Real.rpow_natCast_mul hx0 64 minorDivisorExponent]
    norm_num [minorDivisorExponent]
  have hpow : ((H : ℝ)^2)^minorDivisorExponent≤(A^2)^minorDivisorExponent*(n : ℝ) := by
    have hh := Real.rpow_le_rpow (sq_nonneg (H : ℝ)) hH2 hδ.le
    rwa [Real.mul_rpow (sq_nonneg A) (pow_nonneg hx0 64),he] at hh
  have hfactor : 2*divisorConstant minorDivisorExponent*((H : ℝ)^2)^minorDivisorExponent+4≤
      (2*divisorConstant minorDivisorExponent*(A^2)^minorDivisorExponent+4)*(n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hpow (show 0≤2*divisorConstant minorDivisorExponent by positivity)
    nlinarith only [hh,hx1]
  have hf0 : 0≤2*divisorConstant minorDivisorExponent*((H : ℝ)^2)^minorDivisorExponent+4 := by positivity
  have hh := mul_le_mul hL2 hfactor hf0 (by positivity)
  unfold momentBudget momentPolynomialConstant
  convert hh using 1 <;> ring

end ActualOriginalPolynomialMomentBudget318
