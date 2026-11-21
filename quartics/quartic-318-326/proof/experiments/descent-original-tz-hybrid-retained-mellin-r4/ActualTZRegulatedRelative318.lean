module
public import ActualTZRegulatedZetaAlgebra318
public section
noncomputable section
namespace ActualTZRegulatedRelative318
open scoped BigOperators
open ActualTZRegulatedZetaAlgebra318

variable {I X K : Type*} [NormedField K]

private theorem one_sub_bounds (y : K) (h : ‖y‖ ≤ 1/2) :
    (1:ℝ)/2 ≤ ‖1-y‖ ∧ ‖1-y‖ ≤ 3/2 := by
  have h₀ := norm_add_le (1-y) y
  rw [sub_add_cancel,norm_one] at h₀
  have h₁ := norm_sub_le (1:K) y
  rw [norm_one] at h₁
  constructor <;> linarith

theorem one_site_lower (x z w : K)
    (hx : ‖x‖ ≤ 1/2) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    (1:ℝ)/6 ≤ ‖oneSite x z w‖ := by
  have hz' : ‖x*z‖ ≤ 1/2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hz (norm_nonneg x)).trans (by simpa using hx)
  have hw' : ‖x*w‖ ≤ 1/2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hw (norm_nonneg x)).trans (by simpa using hx)
  have hzw' : ‖x*z*w‖ ≤ 1/2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hw (norm_nonneg (x*z))).trans (by simpa using hz')
  have hlo := (one_sub_bounds _ hzw').1
  have hup := (one_sub_bounds _ hzw').2
  have hnum : (1:ℝ)/4 ≤ ‖1-x*z‖*‖1-x*w‖ := by
    have H := mul_le_mul (one_sub_bounds _ hz').1 (one_sub_bounds _ hw').1
      (by norm_num : (0:ℝ)≤1/2) (norm_nonneg (1-x*z))
    norm_num at H ⊢
    exact H
  rw [oneSite,norm_div,norm_mul]
  exact (le_div_iff₀ (show 0<‖1-x*z*w‖ by linarith)).2 (by linarith)

/-- Lower bound on the actual finite zeta baseline, uniform in any
possibly complex regulators of modulus at most one. -/
theorem baseline_lower (s : Finset I) (x : K) (z w : I → K)
    (hx : ‖x‖ ≤ 1/2) (hz : ∀ i,‖z i‖ ≤ 1) (hw : ∀ i,‖w i‖ ≤ 1) :
    1/(6:ℝ)^s.card ≤ ‖∏ i∈s,oneSite x (z i) (w i)‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.card_insert_of_notMem hi,Finset.prod_insert hi,norm_mul,pow_succ]
    have he : 1/((6:ℝ)^t.card*6)=(1/6)*(1/(6:ℝ)^t.card) := by
      have h6 : (6:ℝ)^t.card ≠ 0 := by positivity
      field_simp [h6] <;> ring
    rw [he]
    exact mul_le_mul (one_site_lower x (z i) (w i) hx (hz i) (hw i)) ih
      (by positivity) (norm_nonneg _)

theorem relative_of_absolute (B E : K) (k : ℕ) (ε : ℝ)
    (hB : 1/(6:ℝ)^k ≤ ‖B‖) (hε : ‖E-B‖ ≤ ε) :
    ‖E/B-1‖ ≤ (6:ℝ)^k*ε := by
  have h6 : 0<(6:ℝ)^k := by positivity
  have hB' : 0<‖B‖ := (by positivity : 0<(1:ℝ)/6^k).trans_le hB
  have hBn : B ≠ 0 := by
    intro he
    rw [he,norm_zero] at hB'
    exact (lt_irrefl 0) hB'
  have he : E/B-1=(E-B)/B := by rw [sub_div,div_self hBn]
  rw [he,norm_div]
  have hh : 1 ≤ (6:ℝ)^k*‖B‖ := by
    simpa only [one_div,mul_comm] using (div_le_iff₀ h6).mp hB
  have hε₀ : 0≤ε := (norm_nonneg _).trans hε
  apply (div_le_iff₀ hB').2
  calc
    _ ≤ ε := hε
    _ = ε*1 := by simp
    _ ≤ ε*((6:ℝ)^k*‖B‖) := mul_le_mul_of_nonneg_left hh hε₀
    _ = _ := by ring

/-- Distinct residue classes give the literal first-order sum. This
relative comparison does not assume an analytic product over primes. -/
theorem noncollision_relative (s : Finset I) (x : K) (z w : I → K)
    (hx : ‖x‖ ≤ 1/2) (hz : ∀ i,‖z i‖ ≤ 1) (hw : ∀ i,‖w i‖ ≤ 1) :
    ‖(1+x*(∑ i∈s,correction (z i) (w i)))/(∏ i∈s,oneSite x (z i) (w i))-1‖ ≤
      (6:ℝ)^s.card*(errorConst s.card*‖x‖^2) := by
  apply relative_of_absolute _ _ _ _ (baseline_lower s x z w hx hz hw)
  rw [norm_sub_rev]
  exact finite_noncollision_bound s x z w hx hz hw

private theorem norm_sum_correction (s : Finset I) (z w : I → K)
    (hz : ∀ i,‖z i‖ ≤ 1) (hw : ∀ i,‖w i‖ ≤ 1) :
    ‖∑ i∈s,correction (z i) (w i)‖ ≤ 3*(s.card:ℝ) := by
  calc
    _ ≤ ∑ i∈s,‖correction (z i) (w i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i∈s,(3:ℝ) := Finset.sum_le_sum fun i _ => correction_bound (z i) (w i) (hz i) (hw i)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,mul_comm]

/-- General relative loss if the grouped local factor only has a
linear estimate. No no-collision assertion is applied to E itself. -/
theorem relative_of_linear (s : Finset I) (x E : K) (z w : I → K) (A : ℝ)
    (hx : ‖x‖ ≤ 1/2) (hz : ∀ i,‖z i‖ ≤ 1) (hw : ∀ i,‖w i‖ ≤ 1)
    (hE : ‖E-1‖ ≤ A*‖x‖) :
    ‖E/(∏ i∈s,oneSite x (z i) (w i))-1‖ ≤
      (6:ℝ)^s.card*((A+3*(s.card:ℝ)+errorConst s.card)*‖x‖) := by
  let B := ∏ i∈s,oneSite x (z i) (w i)
  let S := ∑ i∈s,correction (z i) (w i)
  apply relative_of_absolute _ _ _ _ (baseline_lower s x z w hx hz hw)
  have hs : ‖x*S‖ ≤ (3*(s.card:ℝ))*‖x‖ := by
    rw [norm_mul,mul_comm (3*(s.card:ℝ))]
    exact mul_le_mul_of_nonneg_left (norm_sum_correction s z w hz hw) (norm_nonneg x)
  have hb : ‖(1+x*S)-B‖ ≤ errorConst s.card*‖x‖ := by
    rw [norm_sub_rev]
    calc
      _ ≤ errorConst s.card*‖x‖^2 := finite_noncollision_bound s x z w hx hz hw
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (errorConst_nonneg _)
        simpa only [pow_two,mul_one] using mul_le_mul_of_nonneg_left
          (show ‖x‖≤1 by linarith) (norm_nonneg x)
  change ‖E-B‖ ≤ _
  have he : E-B=((E-1) + -(x*S)) + ((1+x*S)-B) := by ring
  rw [he]
  calc
    _ ≤ (‖E-1‖+‖x*S‖)+‖(1+x*S)-B‖ := by
      exact (norm_add_le _ _).trans (add_le_add_right
        (by simpa only [norm_neg] using norm_add_le (E-1) (-(x*S))) _)
    _ ≤ (A*‖x‖+(3*(s.card:ℝ))*‖x‖)+errorConst s.card*‖x‖ :=
      add_le_add (add_le_add hE hs) hb
    _ = _ := by ring

end ActualTZRegulatedRelative318
