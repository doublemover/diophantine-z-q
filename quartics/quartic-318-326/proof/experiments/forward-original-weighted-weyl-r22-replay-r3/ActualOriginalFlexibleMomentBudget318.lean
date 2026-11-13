module
public import ActualOriginalFlexibleKernelBudget318
public section
noncomputable section
namespace ActualOriginalFlexibleMomentBudget318
open ActualOriginalPolynomialMinorScale318 ActualOriginalFlexibleMinorScale318 ActualOriginalQuadraticEnergyCount318
open ActualDivisorSubpower318

@[expose] def flexibleMomentConstant (p : ℕ) (A : ℝ) : ℝ :=
  (2*A+1)^2*(2*divisorConstant (flexibleDivisorExponent p)*(A^2)^(flexibleDivisorExponent p)+4)

lemma actual_flexible_moment_nonneg (p : ℕ) (A : ℝ) : 0≤flexibleMomentConstant p A := by
  have hh := divisorConstant_pos (flexibleDivisorExponent p) (actual_flexible_exponent_pos p)
  unfold flexibleMomentConstant
  positivity

/-- Fixed delta=1/(16p+64), not a scale-varying divisor exponent. The exact
identity (n^(16p+64))^(1/(16p+64))=n yields a fourth-moment cost O(n^(p*16+65)). -/
theorem actual_flexible_moment (p H n : ℕ) (A : ℝ) (hn : 2≤n)
    (hA : 0≤A) (hH : (H : ℝ)≤A*(n : ℝ)^(p*8+32)) :
    momentBudget H (flexibleDivisorExponent p)≤flexibleMomentConstant p A*(n : ℝ)^(p*16+65) := by
  have hx1 : (1 : ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hx0 : (0 : ℝ)≤n := by positivity
  have hδ : 0<(flexibleDivisorExponent p) := actual_flexible_exponent_pos p
  have hC := divisorConstant_pos (flexibleDivisorExponent p) hδ
  have hx32 : (1 : ℝ)≤(n : ℝ)^(p*8+32) := one_le_pow₀ hx1
  have hL : 2*(H : ℝ)+1≤(2*A+1)*(n : ℝ)^(p*8+32) := by nlinarith
  have hL2 : (2*(H : ℝ)+1)^2≤(2*A+1)^2*(n : ℝ)^(p*16+64) := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤2*(H : ℝ)+1) hL 2
    convert hh using 1 <;> simp only [pow_add,pow_mul] <;> ring
  have hH2 : (H : ℝ)^2≤A^2*(n : ℝ)^(p*16+64) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg H : (0 : ℝ)≤H) hH 2
    convert hh using 1 <;> simp only [pow_add,pow_mul] <;> ring
  have he : ((n : ℝ)^(p*16+64))^(flexibleDivisorExponent p)=(n : ℝ) := by
    rw [←Real.rpow_natCast_mul hx0 (p*16+64) (flexibleDivisorExponent p)]
    have hp : ((p : ℝ)*16+64)≠0 := by positivity
    simp only [flexibleDivisorExponent,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    have he' : ((p : ℝ)*16+64)*(1/((p : ℝ)*16+64))=1 := by field_simp [hp]
    rw [he',Real.rpow_one]
  have hpow : ((H : ℝ)^2)^(flexibleDivisorExponent p)≤(A^2)^(flexibleDivisorExponent p)*(n : ℝ) := by
    have hh := Real.rpow_le_rpow (sq_nonneg (H : ℝ)) hH2 hδ.le
    rwa [Real.mul_rpow (sq_nonneg A) (pow_nonneg hx0 (p*16+64)),he] at hh
  have hfactor : 2*divisorConstant (flexibleDivisorExponent p)*((H : ℝ)^2)^(flexibleDivisorExponent p)+4≤
      (2*divisorConstant (flexibleDivisorExponent p)*(A^2)^(flexibleDivisorExponent p)+4)*(n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hpow (show 0≤2*divisorConstant (flexibleDivisorExponent p) by positivity)
    nlinarith only [hh,hx1]
  have hf0 : 0≤2*divisorConstant (flexibleDivisorExponent p)*((H : ℝ)^2)^(flexibleDivisorExponent p)+4 := by positivity
  have hh := mul_le_mul hL2 hfactor hf0 (by positivity)
  unfold momentBudget flexibleMomentConstant
  convert hh using 1 <;> simp only [pow_add,pow_mul] <;> ring

end ActualOriginalFlexibleMomentBudget318
