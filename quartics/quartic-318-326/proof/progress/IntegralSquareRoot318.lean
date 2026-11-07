module
public import IntegralScaledNorm318
public section
namespace IntegralSquareRoot318
open PowerSeries IntegralRingEvaluation318 IntegralScaledSeries318 IntegralScaledBounds318
variable (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
variable {R : Type*} [NormedCommRing R] [CompleteSpace R] [IsUltrametricDist R] [NormBoundOne R]
variable (ι : ℤ_[p] →+* R) (D : R) (hι : Isometry ι)
set_option linter.unusedSectionVars false

/-- Integral coefficient identity before evaluation, requiring no ambient-field hypothesis. -/
theorem B_square : (1-C (parameter p D)*X)*(B p hp ι D)^2=1 := by
  have hz : (1-C ((p : ℤ_[p])^4)*X)*
      (ScaledCoefficients318.Bscaled p hp 1 (by simp))^2=1 := by
    apply ScaledFormalSeries318.powerSeries_map_injective p
    simp only [map_mul, map_sub, map_one, map_pow, map_X,
      map_natCast, ScaledCoefficients318.map_Bscaled, one_mul]
    have h := congrArg (rescale ((p : ℚ_[p])^4))
      (GenericFormalDifferential318.B_square (K := ℚ_[p]))
    simpa only [map_mul, map_sub, map_one, map_pow, rescale_X, map_natCast] using h
  have h := congrArg (fun f : PowerSeries ℤ_[p] => rescale D (f.map ι)) hz
  simpa only [map_mul, map_sub, map_one, map_C, map_pow, map_X, map_natCast,
    rescale_X, B, parameter, mul_assoc, mul_left_comm] using h

include hι in
theorem eval_B_square (t : R) :
    (1-parameter p D*t)*(eval R (B p hp ι D) t)^2=1 := by
  have h := congrArg (fun f : PowerSeries R => eval R f t) (B_square p hp ι D)
  have hb := B_restricted p hp ι D hι
  have hx := X_restricted R
  have hc : Restricted R (C (parameter p D)) := isRestricted_C 1 _
  have h1 : Restricted R (1 : PowerSeries R) := isRestricted_one 1
  simpa only [eval_mul R _ _ (h1.sub (hc.mul hx)) (hb.pow 2),
    eval_sub R _ _ h1 (hc.mul hx), eval_one, eval_mul R _ _ hc hx,
    eval_C, eval_X, eval_pow R _ hb] using h

/-- The positive local square root for any integral input, not only fourth powers. -/
@[expose] noncomputable def root (t : R) : R :=
  (1-parameter p D*t)*eval R (B p hp ι D) t

include hι in
theorem root_square (t : R) : (root p hp ι D t)^2=1-parameter p D*t := by
  have h := eval_B_square p hp ι D hι t
  unfold root
  calc
    _ = (1-parameter p D*t)*((1-parameter p D*t)*(eval R (B p hp ι D) t)^2) := by ring
    _ = _ := by rw [h, mul_one]

include hι in
theorem root_error (t : R) : ‖root p hp ι D t-1‖ ≤ ‖(p : ℚ_[p])‖^4 := by
  let b := eval R (B p hp ι D) t
  let a := parameter p D*t
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
      (B_error p hp ι D hι t)
  · simpa only [norm_neg] using ha

include hι in
theorem root_isUnit (t : R) : IsUnit (root p hp ι D t) :=
  isUnit_of_near_one _ ((root_error p hp ι D hι t).trans_lt
    (ScaledDecay318.ratio_lt_one p 4 (by decide)))

include hι in
theorem root_norm (t : R) : ‖root p hp ι D t‖=1 :=
  IntegralScaledNorm318.norm_of_isUnit p ι hι _ (root_isUnit p hp ι D hι t)

end IntegralSquareRoot318
#print axioms IntegralSquareRoot318.B_square
#print axioms IntegralSquareRoot318.eval_B_square
#print axioms IntegralSquareRoot318.root_square
#print axioms IntegralSquareRoot318.root_error
#print axioms IntegralSquareRoot318.root_isUnit
#print axioms IntegralSquareRoot318.root_norm
