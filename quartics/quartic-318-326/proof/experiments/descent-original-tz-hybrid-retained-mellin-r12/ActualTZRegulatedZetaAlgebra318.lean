module
public import Mathlib
public section
noncomputable section
namespace ActualTZRegulatedZetaAlgebra318
open scoped BigOperators

variable {K : Type*} [NormedField K]

@[expose] def correction (z w : K) : K := (1-z)*(1-w)-1

@[expose] def oneSite (x z w : K) : K := ((1-x*z)*(1-x*w))/(1-x*z*w)

theorem correction_eq (z w : K) : correction z w = -z-w+z*w := by
  unfold correction
  ring

/-- Denominator-cleared first-order comparison at an actual one-row
two-divisor local factor, retaining the same-prime overlap z*w. -/
theorem cleared (x z w : K) :
    (1-x*z)*(1-x*w)-(1-x*z*w)*(1+x*correction z w) =
      x^2*z*w*(1-z)*(1-w) := by
  unfold correction
  ring

theorem remainder_eq (x z w : K) (h : 1-x*z*w ≠ 0) :
    oneSite x z w-(1+x*correction z w) =
      x^2*z*w*(1-z)*(1-w)/(1-x*z*w) := by
  unfold oneSite
  field_simp [h]
  unfold correction
  ring

private theorem norm_product_le (x z w : K) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖x*z*w‖ ≤ ‖x‖ := by
  calc
    _ = ‖x‖*‖z‖*‖w‖ := by simp only [norm_mul]
    _ ≤ ‖x‖*‖z‖*1 := mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ ‖x‖*1*1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hz (norm_nonneg _)) zero_le_one
    _ = _ := by simp

theorem denominator_lower (x z w : K) (hx : ‖x‖ ≤ 1/2) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    (1:ℝ)/2 ≤ ‖1-x*z*w‖ := by
  have hsum : (1:ℝ) ≤ ‖1-x*z*w‖+‖x*z*w‖ := by
    calc
      _ = ‖(1-x*z*w)+x*z*w‖ := by rw [sub_add_cancel,norm_one]
      _ ≤ _ := norm_add_le _ _
  linarith [norm_product_le x z w hz hw]

theorem correction_bound (z w : K) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖correction z w‖ ≤ 3 := by
  rw [correction_eq]
  calc
    _ ≤ ‖-z-w‖+‖z*w‖ := norm_add_le _ _
    _ ≤ ‖z‖+‖w‖+‖z‖*‖w‖ := by
      rw [norm_mul]
      apply add_le_add_right
      simpa only [norm_neg] using norm_sub_le (-z) w
    _ ≤ 3 := by
      have h := mul_le_mul hz hw (norm_nonneg _) zero_le_one
      linarith

theorem one_site_bound (x z w : K) (hx : ‖x‖ ≤ 1/2) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖oneSite x z w-(1+x*correction z w)‖ ≤ 8*‖x‖^2 := by
  have hl := denominator_lower x z w hx hz hw
  have hden : 1-x*z*w ≠ 0 := by
    intro h
    rw [h,norm_zero] at hl
    norm_num at hl
  have hz' : ‖1-z‖ ≤ 2 := by
    calc
      _ ≤ ‖(1:K)‖+‖z‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_one]; linarith
  have hw' : ‖1-w‖ ≤ 2 := by
    calc
      _ ≤ ‖(1:K)‖+‖w‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_one]; linarith
  rw [remainder_eq x z w hden,norm_div]
  simp only [norm_mul,norm_pow]
  apply (div_le_iff₀ (show 0<‖1-x*z*w‖ by linarith)).2
  have ht : ‖x‖^2*‖z‖*‖w‖*‖1-z‖*‖1-w‖ ≤ 4*‖x‖^2 := by
    calc
      _ ≤ ‖x‖^2*(1:ℝ)*1*2*2 := by gcongr <;> first | assumption | positivity
      _ = _ := by ring
  have hb := mul_le_mul_of_nonneg_left hl (show 0≤8*‖x‖^2 by positivity)
  linarith

/-- Exact step when multiplying another one-row baseline into a
finite noncollision Euler approximation. The last term is quadratic
in 1/p; the linear terms are the literal sum over original rows. -/
theorem finite_step (x B P S u : K) :
    B*P-(1+x*(u+S)) =
      B*(P-(1+x*S))+(B-(1+x*u))*(1+x*S)+x^2*u*S := by
  ring


private theorem one_site_norm (x z w : K) (hx : ‖x‖ ≤ 1/2) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖oneSite x z w‖ ≤ 5 := by
  have h := norm_add_le (oneSite x z w-(1+x*correction z w)) (1+x*correction z w)
  rw [sub_add_cancel] at h
  have hs := norm_add_le (1:K) (x*correction z w)
  rw [norm_one,norm_mul] at hs
  have ht : ‖x‖^2 ≤ (1:ℝ)/4 := by
    simpa only [pow_two,show (1:ℝ)/2*(1/2)=1/4 by norm_num] using
      mul_le_mul hx hx (norm_nonneg x) (by norm_num : (0:ℝ)≤1/2)
  have hu : ‖x‖*‖correction z w‖ ≤ (1:ℝ)/2*3 :=
    mul_le_mul hx (correction_bound z w hz hw) (norm_nonneg _) (by norm_num)
  linarith [one_site_bound x z w hx hz hw]

def errorConst : ℕ → ℝ
  | 0 => 0
  | n+1 => 5*errorConst n+8+33*(n:ℝ)

theorem errorConst_nonneg (n : ℕ) : 0≤errorConst n := by
  induction n with
  | zero => simp [errorConst]
  | succ n ih =>
    rw [errorConst]
    positivity

/-- Summed first-order local factor across the DISTINCT original
roots. Its finite baseline has a quadratic error with constant
depending only on the number of positions, not on p, W or the tuple. -/
theorem finite_noncollision_bound {I : Type*} (s : Finset I) (x : K) (z w : I → K)
    (hx : ‖x‖ ≤ 1/2) (hz : ∀ i,‖z i‖ ≤ 1) (hw : ∀ i,‖w i‖ ≤ 1) :
    ‖(∏ i∈s,oneSite x (z i) (w i))-(1+x*(∑ i∈s,correction (z i) (w i)))‖ ≤
      errorConst s.card*‖x‖^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [errorConst]
  | @insert i t hi ih =>
    let B := oneSite x (z i) (w i)
    let P := ∏ j∈t,oneSite x (z j) (w j)
    let S := ∑ j∈t,correction (z j) (w j)
    let u := correction (z i) (w i)
    have h0 : ‖B‖ ≤ 5 := one_site_norm x (z i) (w i) hx (hz i) (hw i)
    have h1 : ‖u‖ ≤ 3 := correction_bound (z i) (w i) (hz i) (hw i)
    have h2 : ‖B-(1+x*u)‖ ≤ 8*‖x‖^2 := one_site_bound x (z i) (w i) hx (hz i) (hw i)
    have h3 : ‖S‖ ≤ 3*(t.card:ℝ) := by
      calc
        _ ≤ ∑ j∈t,‖correction (z j) (w j)‖ := norm_sum_le _ _
        _ ≤ ∑ _j∈t,(3:ℝ) := Finset.sum_le_sum fun j _ =>
          correction_bound (z j) (w j) (hz j) (hw j)
        _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,mul_comm]
    have h4 : ‖1+x*S‖ ≤ 1+3*(t.card:ℝ) := by
      have H := norm_add_le (1:K) (x*S)
      rw [norm_one,norm_mul] at H
      have G := mul_le_mul (show ‖x‖≤1 by linarith) h3 (norm_nonneg S) zero_le_one
      linarith
    rw [Finset.prod_insert hi,Finset.sum_insert hi,Finset.card_insert_of_notMem hi,errorConst]
    change ‖B*P-(1+x*(u+S))‖ ≤ (5*errorConst t.card+8+33*(t.card:ℝ))*‖x‖^2
    rw [finite_step]
    calc
      _ ≤ ‖B*(P-(1+x*S))‖+‖(B-(1+x*u))*(1+x*S)‖+‖x^2*u*S‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ 5*(errorConst t.card*‖x‖^2)+(8*‖x‖^2)*(1+3*(t.card:ℝ))+
          ‖x‖^2*3*(3*(t.card:ℝ)) := by
        simp only [norm_mul,norm_pow]
        gcongr <;> first | assumption | positivity
      _ = _ := by ring

end ActualTZRegulatedZetaAlgebra318
