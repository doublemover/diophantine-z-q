module
public import IntegralScaledSeries318
public import RestrictedBranch318
public import Mathlib.Analysis.SpecificLimits.Normed
public section
namespace IntegralScaledBounds318
open PowerSeries IntegralRingEvaluation318 IntegralScaledSeries318
variable (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
variable {R : Type*} [NormedCommRing R] [CompleteSpace R] [IsUltrametricDist R] [NormBoundOne R]
variable (ι : ℤ_[p] →+* R) (D : R) (hι : Isometry ι)
set_option linter.unusedSectionVars false

include hι in
theorem inclusion_norm (z : ℤ_[p]) : ‖ι z‖=‖z‖ := by
  simpa only [map_zero, dist_zero_right] using hι.dist_eq z 0

include hι in
theorem prime_norm : ‖(p : R)‖=‖(p : ℚ_[p])‖ := by
  have h := inclusion_norm p ι hι (p : ℤ_[p])
  simpa only [map_natCast, ←PadicInt.norm_coe, PadicInt.coe_natCast] using h

theorem H_zero : coeff 0 (H p hp ι D)=1 := by
  simp only [H, coeff_rescale, pow_zero, coeff_map, one_mul,
    RestrictedBranch318.Hscaled_zero, map_one]

theorem B_zero : coeff 0 (B p hp ι D)=1 := by
  simp only [B, coeff_rescale, pow_zero, coeff_map, one_mul,
    RestrictedBranch318.Bscaled_zero, map_one]

include hι in
theorem H_coefficient_decay (n : ℕ) :
    ‖coeff n (H p hp ι D)‖ ≤ (‖(p : ℚ_[p])‖^3)^n := by
  rw [H, coeff_rescale, coeff_map]
  calc
    _ ≤ ‖ι (coeff n (ScaledCoefficients318.Hscaled p hp 1 (by simp)))‖ :=
      (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (NormBoundOne.norm_le_one _))
    _ = ‖coeff n (ScaledCoefficients318.Hscaled p hp 1 (by simp))‖ := inclusion_norm p ι hι _
    _ ≤ _ := by
      rw [←PadicInt.norm_coe]
      simp only [ScaledCoefficients318.coeff_Hscaled, ScaledCoefficients318.coe_hIntegralCoefficient]
      exact ScaledDecay318.hCoefficient_decay p hp 1 (by simp) n

include hι in
theorem B_coefficient_decay (n : ℕ) :
    ‖coeff n (B p hp ι D)‖ ≤ (‖(p : ℚ_[p])‖^4)^n := by
  rw [B, coeff_rescale, coeff_map]
  calc
    _ ≤ ‖ι (coeff n (ScaledCoefficients318.Bscaled p hp 1 (by simp)))‖ :=
      (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (NormBoundOne.norm_le_one _))
    _ = ‖coeff n (ScaledCoefficients318.Bscaled p hp 1 (by simp))‖ := inclusion_norm p ι hι _
    _ ≤ _ := by
      rw [←PadicInt.norm_coe]
      simp only [ScaledCoefficients318.coeff_Bscaled, ScaledCoefficients318.coe_bIntegralCoefficient]
      exact ScaledDecay318.bCoefficient_decay p hp 1 (by simp) n

include hι in
theorem H_error (t : R) : ‖eval R (H p hp ι D) t-1‖ ≤ ‖(p : ℚ_[p])‖^3 := by
  have hs := monomial_summable R _ (H_restricted p hp ι D hι) t
  rw [eval, hs.tsum_eq_zero_add, H_zero, pow_zero, mul_one, add_sub_cancel_left]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  calc
    _ ≤ ‖coeff (n+1) (H p hp ι D)‖ :=
      (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (NormBoundOne.norm_le_one _))
    _ ≤ (‖(p : ℚ_[p])‖^3)^(n+1) := H_coefficient_decay p hp ι D hι (n+1)
    _ ≤ _ := by
      simpa using pow_le_pow_of_le_one (pow_nonneg (norm_nonneg (p : ℚ_[p])) 3)
        (ScaledDecay318.ratio_lt_one p 3 (by decide)).le (show 1≤n+1 by omega)

include hι in
theorem B_error (t : R) : ‖eval R (B p hp ι D) t-1‖ ≤ ‖(p : ℚ_[p])‖^4 := by
  have hs := monomial_summable R _ (B_restricted p hp ι D hι) t
  rw [eval, hs.tsum_eq_zero_add, B_zero, pow_zero, mul_one, add_sub_cancel_left]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  calc
    _ ≤ ‖coeff (n+1) (B p hp ι D)‖ :=
      (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (NormBoundOne.norm_le_one _))
    _ ≤ (‖(p : ℚ_[p])‖^4)^(n+1) := B_coefficient_decay p hp ι D hι (n+1)
    _ ≤ _ := by
      simpa using pow_le_pow_of_le_one (pow_nonneg (norm_nonneg (p : ℚ_[p])) 4)
        (ScaledDecay318.ratio_lt_one p 4 (by decide)).le (show 1≤n+1 by omega)

include hι in
theorem parameter_norm : ‖parameter p D‖ ≤ ‖(p : ℚ_[p])‖^4 := by
  unfold parameter
  calc
    _ ≤ ‖(p : R)^4‖ := (norm_mul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (NormBoundOne.norm_le_one D))
    _ ≤ ‖(p : R)‖^4 := norm_pow_le' _ (by decide)
    _ = _ := by rw [prime_norm p ι hι]

include hι in
theorem eval_branch (t : R) : eval R (branch p hp ι D) t =
    (1-parameter p D*t^4)*eval R (B p hp ι D) (t^4) := by
  have hx := X_restricted R
  have hc : Restricted R (C (parameter p D)) := isRestricted_C 1 _
  have h1 : Restricted R (1 : PowerSeries R) := isRestricted_one 1
  rw [branch, eval_mul R _ _ (h1.sub (hc.mul (hx.pow 4)))
    (differential_restricted p hp ι D hι),
    eval_sub R _ _ h1 (hc.mul (hx.pow 4)), eval_one,
    eval_mul R _ _ hc (hx.pow 4), eval_C, eval_pow R _ hx, eval_X,
    differential, eval_subst R _ _ (B_restricted p hp ι D hι) (hx.pow 4) (by simp),
    eval_pow R _ hx, eval_X]

include hι in
theorem branch_error (t : R) : ‖eval R (branch p hp ι D) t-1‖ ≤ ‖(p : ℚ_[p])‖^4 := by
  rw [eval_branch p hp ι D hι]
  let b := eval R (B p hp ι D) (t^4)
  let a := parameter p D*t^4
  change ‖(1-a)*b-1‖ ≤ _
  have he : (1-a)*b-1=(1-a)*(b-1)-a := by ring
  have ha : ‖a‖ ≤ ‖(p : ℚ_[p])‖^4 :=
    ((norm_mul_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (NormBoundOne.norm_le_one _))).trans
      (parameter_norm p ι D hι)
  rw [he, sub_eq_add_neg]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · exact ((norm_mul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (NormBoundOne.norm_le_one _))).trans
      (B_error p hp ι D hι (t^4))
  · simpa only [norm_neg] using ha

/-- Actual Neumann-series unit criterion in the complete integral ring. -/
theorem isUnit_of_near_one (x : R) (hx : ‖x-1‖<1) : IsUnit x := by
  have hh : ‖1-x‖<1 := by simpa only [norm_sub_rev] using hx
  have hu := isUnit_one_sub_of_norm_lt_one hh
  simpa only [sub_sub_cancel] using hu

include hι in
theorem H_isUnit (t : R) : IsUnit (eval R (H p hp ι D) t) :=
  isUnit_of_near_one _ ((H_error p hp ι D hι t).trans_lt (ScaledDecay318.ratio_lt_one p 3 (by decide)))

include hι in
theorem B_isUnit (t : R) : IsUnit (eval R (B p hp ι D) t) :=
  isUnit_of_near_one _ ((B_error p hp ι D hι t).trans_lt (ScaledDecay318.ratio_lt_one p 4 (by decide)))

include hι in
theorem branch_isUnit (t : R) : IsUnit (eval R (branch p hp ι D) t) :=
  isUnit_of_near_one _ ((branch_error p hp ι D hι t).trans_lt (ScaledDecay318.ratio_lt_one p 4 (by decide)))

include hι in
theorem H_map_ne_zero {K : Type*} [Semiring K] [Nontrivial K] (φ : R →+* K) (t : R) :
    φ (eval R (H p hp ι D) t) ≠ 0 := ((H_isUnit p hp ι D hι t).map φ).ne_zero

include hι in
theorem B_map_ne_zero {K : Type*} [Semiring K] [Nontrivial K] (φ : R →+* K) (t : R) :
    φ (eval R (B p hp ι D) t) ≠ 0 := ((B_isUnit p hp ι D hι t).map φ).ne_zero

include hι in
theorem branch_map_ne_zero {K : Type*} [Semiring K] [Nontrivial K] (φ : R →+* K) (t : R) :
    φ (eval R (branch p hp ι D) t) ≠ 0 := ((branch_isUnit p hp ι D hι t).map φ).ne_zero


/-- Isometric ambient-field inclusions preserve the quantitative branch choice. -/
theorem norm_map_sub_one {K : Type*} [NormedRing K] (φ : R →+* K)
    (hφ : Isometry φ) (x : R) : ‖φ x-1‖=‖x-1‖ := by
  have hh := hφ.dist_eq (x-1) 0
  simpa only [map_sub, map_one, map_zero, dist_zero_right] using hh

include hι in
theorem H_map_error {K : Type*} [NormedRing K] (φ : R →+* K) (hφ : Isometry φ) (t : R) :
    ‖φ (eval R (H p hp ι D) t)-1‖ ≤ ‖(p : ℚ_[p])‖^3 := by
  rw [norm_map_sub_one φ hφ]
  exact H_error p hp ι D hι t

include hι in
theorem B_map_error {K : Type*} [NormedRing K] (φ : R →+* K) (hφ : Isometry φ) (t : R) :
    ‖φ (eval R (B p hp ι D) t)-1‖ ≤ ‖(p : ℚ_[p])‖^4 := by
  rw [norm_map_sub_one φ hφ]
  exact B_error p hp ι D hι t

include hι in
theorem branch_map_error {K : Type*} [NormedRing K] (φ : R →+* K) (hφ : Isometry φ) (t : R) :
    ‖φ (eval R (branch p hp ι D) t)-1‖ ≤ ‖(p : ℚ_[p])‖^4 := by
  rw [norm_map_sub_one φ hφ]
  exact branch_error p hp ι D hι t

include hι in
theorem H_map_near_one {K : Type*} [NormedRing K] (φ : R →+* K) (hφ : Isometry φ) (t : R) :
    ‖φ (eval R (H p hp ι D) t)-1‖ < 1 :=
  (H_map_error p hp ι D hι φ hφ t).trans_lt (ScaledDecay318.ratio_lt_one p 3 (by decide))

include hι in
theorem B_map_near_one {K : Type*} [NormedRing K] (φ : R →+* K) (hφ : Isometry φ) (t : R) :
    ‖φ (eval R (B p hp ι D) t)-1‖ < 1 :=
  (B_map_error p hp ι D hι φ hφ t).trans_lt (ScaledDecay318.ratio_lt_one p 4 (by decide))

include hι in
theorem branch_map_near_one {K : Type*} [NormedRing K] (φ : R →+* K) (hφ : Isometry φ) (t : R) :
    ‖φ (eval R (branch p hp ι D) t)-1‖ < 1 :=
  (branch_map_error p hp ι D hι φ hφ t).trans_lt (ScaledDecay318.ratio_lt_one p 4 (by decide))

end IntegralScaledBounds318
#print axioms IntegralScaledBounds318.H_error
#print axioms IntegralScaledBounds318.B_error
#print axioms IntegralScaledBounds318.branch_error
#print axioms IntegralScaledBounds318.branch_isUnit
#print axioms IntegralScaledBounds318.H_map_ne_zero
#print axioms IntegralScaledBounds318.branch_map_ne_zero

#print axioms IntegralScaledBounds318.branch_map_near_one
