module
public import EulerProduct318
public import E4Producer318
public section
noncomputable section
open Function Metric
namespace ActualQJ318
set_option maxHeartbeats 0

/-- The normalized analytic modular j-invariant, defined from Mathlib's
actual normalized weight-four Eisenstein series and modular discriminant. -/
@[expose] def jInvariant (tau:UpperHalfPlane) : ℂ :=
  (ModularForm.E (k:=4) (by norm_num) tau)^3 / ModularForm.discriminant tau

/-- The actual holomorphic regularization q*j at the cusp, including q=0. -/
@[expose] def G (q:ℂ) : ℂ :=
  (E4Producer318.E4 q)^3/(EulerProduct318.product q)^24

theorem G_zero : G 0=1 := by
  simp [G,E4Producer318.E4_zero,EulerProduct318.product_zero]

theorem G_differentiableAt (q:ℂ) (hq:‖q‖<1) : DifferentiableAt ℂ G q := by
  apply DifferentiableAt.div
  · exact (E4Producer318.E4_holomorphic.differentiableAt
      (isOpen_ball.mem_nhds (by simpa using hq))).pow 3
  · exact (EulerProduct318.product_differentiableAt q hq).pow 24
  · exact pow_ne_zero _ (EulerProduct318.product_ne_zero q hq)

theorem G_holomorphic : DifferentiableOn ℂ G (ball 0 1) := by
  intro q hq
  exact (G_differentiableAt q (by simpa using hq)).differentiableWithinAt

theorem G_bound (q:ℂ) (hq:‖q‖≤(1:ℝ)/100) : ‖G q‖<128 := by
  have he:=E4Producer318.E4_bound hq
  have hp:=EulerProduct318.inverse_pow_bound q hq
  have he3:‖E4Producer318.E4 q‖^3≤(4:ℝ)^3 :=
    pow_le_pow_left₀ (norm_nonneg _) he.le 3
  rw [G,div_eq_mul_inv,norm_mul,norm_pow,←inv_pow]
  calc
    _ ≤ 4^3*‖(EulerProduct318.product q)⁻¹^24‖ := mul_le_mul_of_nonneg_right he3 (norm_nonneg _)
    _ < 128 := by nlinarith

theorem G_qParam (tau:UpperHalfPlane) :
    G (Periodic.qParam 1 tau)=Periodic.qParam 1 tau*jInvariant tau := by
  have hq:Periodic.qParam 1 (tau:ℂ)≠0:=Periodic.qParam_ne_zero _
  rw [G,E4Producer318.E4_qParam,jInvariant,EulerProduct318.discriminant_qParam]
  field_simp

/-- The three analytic G inputs used by the cusp estimates are actual
proved properties of q*j, not assumptions about an unrelated function. -/
theorem cusp_G_data :
    (∀q:ℂ,‖q‖≤(1:ℝ)/100 → DifferentiableAt ℂ G q) ∧
    (∀q:ℂ,‖q‖≤(1:ℝ)/100 → ‖G q‖≤128) ∧ G 0=1 := by
  refine ⟨?_,?_,G_zero⟩
  · intro q hq
    apply G_differentiableAt q
    linarith
  · intro q hq
    exact (G_bound q hq).le

/-- An actual selected j-value supplies the exact regularized value equation. -/
theorem selected_value (tau:UpperHalfPlane) (i:ℕ)
    (hvalue:jInvariant tau=1728*((2:ℂ)^128+i)) :
    G (Periodic.qParam 1 tau)=Periodic.qParam 1 tau*(1728*((2:ℂ)^128+i)) := by
  rw [G_qParam,hvalue]

end ActualQJ318
#print axioms ActualQJ318.G_qParam
#print axioms ActualQJ318.cusp_G_data
