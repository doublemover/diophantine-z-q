module
public import ActualPreparedPoleSquarefreeClasses318
public import ActualTwoDescentCloseSquare318
public section
noncomputable section
namespace ActualPreparedPoleLocalSquares318
open ActualPreparedPoleSquarefreeClasses318

/-- Transport an actual root of b/17 to the SAME positive squarefree beta.
No new choice of pole or squareclass occurs. -/
theorem beta_root {K : Type*} [Field K] [CharZero K]
    {b : ℚ} (C : Classes b) (r : K) (hr : r^2=(b:K)/17) :
    ∃ u : K, u≠0 ∧ u^2=(C.beta:K) := by
  have hc : (C.c:K)≠0 := by exact_mod_cast C.c_ne
  have hf : (17:K)*(b:K)=(C.beta:K)*(C.c:K)^2 := by
    exact_mod_cast C.first_class
  have he : ((17:K)*r/(C.c:K))^2=(C.beta:K) := by
    rw [div_pow,mul_pow,hr]
    have h17 : (17:K)≠0 := by norm_num
    have hn : (17:K)^2*((b:K)/17)=17*(b:K) := by
      field_simp [h17]
      <;> ring
    rw [hn,hf]
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hc)
  exact ⟨17*r/(C.c:K),by
    intro hu
    have hz : (C.beta:K)=0 := by simpa only [hu,zero_pow (by decide : (2:ℕ)≠0)] using he.symm
    exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt C.beta_pos)) hz,he⟩

/-- The complementary root is multiplied by the ORIGINAL factor17b/d. -/
theorem theta_root {K : Type*} [Field K] [CharZero K]
    {b : ℚ} (C : Classes b) (r : K) (hr : r^2=1-(b:K)/17) :
    ∃ u : K, u≠0 ∧ u^2=(C.theta:K) := by
  have hd : (C.d:K)≠0 := by exact_mod_cast C.d_ne
  have hf : ((17:K)*(b:K))^2*(1-(b:K)/17)=(C.theta:K)*(C.d:K)^2 := by
    exact_mod_cast C.second_class
  have he : (((17:K)*(b:K))*r/(C.d:K))^2=(C.theta:K) := by
    rw [div_pow,mul_pow,hr]
    rw [hf]
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hd)
  refine ⟨((17:K)*(b:K))*r/(C.d:K),?_,he⟩
  intro hu
  have hz : (C.theta:K)=0 := by simpa only [hu,zero_pow (by decide : (2:ℕ)≠0)] using he.symm
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt C.theta_pos)) hz

/-- At an odd prime where b/17 is small, the ACTUAL complement supplies
a square root of theta. Deriving this norm bound from support membership is
a separate valuation obligation, not an implicit hypothesis discharge. -/
theorem theta_at_small_pole {p : ℕ} [Fact p.Prime] (hp2 : p≠2)
    {b : ℚ} (C : Classes b) (hsmall : ‖(b:ℚ_[p])/17‖<1) :
    ∃ u : ℚ_[p], u≠0 ∧ u^2=(C.theta:ℚ_[p]) := by
  obtain ⟨r,_,hr⟩ := ActualTwoDescentCloseSquare318.actual_close_one_square hp2
    (1-(b:ℚ_[p])/17) (by
      have he : (1-(b:ℚ_[p])/17)-1 = -((b:ℚ_[p])/17) := by ring
      rw [he,norm_neg]
      exact hsmall)
  exact theta_root C r hr

/-- At an odd prime where b/17 is near1, the SAME beta is a square. -/
theorem beta_at_near_seventeen {p : ℕ} [Fact p.Prime] (hp2 : p≠2)
    {b : ℚ} (C : Classes b) (hnear : ‖(b:ℚ_[p])/17-1‖<1) :
    ∃ u : ℚ_[p], u≠0 ∧ u^2=(C.beta:ℚ_[p]) := by
  obtain ⟨r,_,hr⟩ := ActualTwoDescentCloseSquare318.actual_close_one_square hp2
    ((b:ℚ_[p])/17) hnear
  exact beta_root C r hr

end ActualPreparedPoleLocalSquares318
