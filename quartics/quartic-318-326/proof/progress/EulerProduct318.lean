module
public import CMEta318
public import Mathlib.NumberTheory.ModularForms.Discriminant
public section
noncomputable section
open MeasureTheory Metric Function Filter
open scoped Topology
namespace EulerProduct318
set_option maxHeartbeats 0

/-- The actual convergent Euler product used in the modular discriminant. -/
@[expose] def product (q:ℂ) : ℂ := ∏'n:ℕ,(1-q^(n+1))

theorem product_ne_zero (q:ℂ) (hq:‖q‖<1) : product q≠0 := by
  have hs:Summable (fun n:ℕ=>-q^(n+1)) := by
    apply summable_norm_iff.mp
    simpa only [norm_neg,norm_pow] using
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq)
  simpa only [product,sub_eq_add_neg] using tprod_one_add_ne_zero_of_summable
    (fun n=>by simpa only [sub_eq_add_neg] using (norm_pos_iff.mp (CMEta318.factor_pos q hq n))) hs.norm

theorem product_zero : product 0=1 := by simp [product]

theorem product_holomorphic : DifferentiableOn ℂ product (ball 0 1) :=
  ModularForm.differentiableOn_tprod_one_sub_pow

theorem product_differentiableAt (q:ℂ) (hq:‖q‖<1) : DifferentiableAt ℂ product q :=
  product_holomorphic.differentiableAt (isOpen_ball.mem_nhds (by simpa using hq))

/-- A generous uniform bound on the actual inverse discriminant product. -/
theorem inverse_pow_bound (q:ℂ) (hq:‖q‖≤(1:ℝ)/100) : ‖(product q)⁻¹^24‖<2 := by
  have hq1:‖q‖<1 := by linarith
  have hp0:0<‖product q‖ := norm_pos_iff.mpr (product_ne_zero q hq1)
  have hb:=CMEta318.tprod_log_bound q hq1
  change -Real.log ‖product q‖≤‖q‖/(1-‖q‖)^2 at hb
  have hrat:‖q‖/(1-‖q‖)^2≤100/9801 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0<1-‖q‖))).mpr
    have hh : (99:ℝ)/100≤1-‖q‖ := by linarith
    have hs : ((99:ℝ)/100)^2≤(1-‖q‖)^2 := sq_le_sq₀ (by norm_num) (by linarith) |>.mpr hh
    nlinarith
  have hl : Real.log ‖(product q)⁻¹^24‖<Real.log 2 := by
    rw [norm_pow,norm_inv,Real.log_pow,Real.log_inv]
    norm_num only [Nat.cast_ofNat]
    have hlow:=Real.log_two_gt_d9
    nlinarith [hb.trans hrat]
  exact (Real.log_lt_log_iff (norm_pos_iff.mpr (pow_ne_zero _ (inv_ne_zero (product_ne_zero q hq1)))) (by norm_num : (0:ℝ)<2)).mp hl

/-- Exact binding of the product to Mathlib's actual modular discriminant. -/
theorem discriminant_qParam (tau:UpperHalfPlane) :
    ModularForm.discriminant tau=Periodic.qParam 1 tau*(product (Periodic.qParam 1 tau))^24 := by
  rw [ModularForm.discriminant_eq_q_prod]
  congr 1
  have hq:‖Periodic.qParam 1 (tau:ℂ)‖<1:=Periodic.norm_qParam_lt_one one_pos tau.im_pos
  simpa only [product,ModularForm.eta_q] using
    (ModularForm.multipliable_one_sub_pow hq).tprod_pow 24

end EulerProduct318
#print axioms EulerProduct318.inverse_pow_bound
#print axioms EulerProduct318.discriminant_qParam
