module
public import PeriodEisenstein318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace UniformPeriodBounds318
set_option maxHeartbeats 0

@[expose] def period (v : Fin 2 → ℤ) (z : ℂ) : ℂ := (v 0:ℂ)*z+v 1

lemma period_im (v : Fin 2 → ℤ) (z : ℂ) : (period v z).im=(v 0:ℝ)*z.im := by
  simp [period,Complex.mul_im]

lemma period_sub (v : Fin 2 → ℤ) (z w : ℂ) :
    period v z-period v w=(v 0:ℂ)*(z-w) := by
  unfold period
  ring

lemma first_coefficient_bound (tau : UpperHalfPlane) (v : Fin 2 → ℤ) :
    |(v 0:ℝ)| *tau.im ≤ ‖period v (tau:ℂ)‖ := by
  have hi := Complex.abs_im_le_norm (period v (tau:ℂ))
  rw [period_im] at hi
  change |(v 0:ℝ)*tau.im|≤‖period v (tau:ℂ)‖ at hi
  simpa only [abs_mul,abs_of_pos tau.im_pos] using hi

lemma variation_bound (tau : UpperHalfPlane) (v : Fin 2 → ℤ) (z : ℂ)
    (hz : ‖z-(tau:ℂ)‖≤tau.im/2) :
    ‖period v z-period v (tau:ℂ)‖≤‖period v (tau:ℂ)‖/2 := by
  rw [period_sub,norm_mul]
  have hn : ‖(v 0:ℂ)‖=|(v 0:ℝ)| := Complex.norm_intCast _
  rw [hn]
  have hmul := mul_le_mul_of_nonneg_left hz (abs_nonneg (v 0:ℝ))
  have hm := first_coefficient_bound tau v
  nlinarith

/-- Simultaneous lower and upper period bounds, uniform in both integer coefficients. -/
theorem period_bounds (tau : UpperHalfPlane) (v : Fin 2 → ℤ) (z : ℂ)
    (hz : ‖z-(tau:ℂ)‖≤tau.im/2) :
    ‖period v (tau:ℂ)‖/2 ≤ ‖period v z‖ ∧
      ‖period v z‖ ≤ 3*‖period v (tau:ℂ)‖/2 := by
  have hd := variation_bound tau v z hz
  have hlo := norm_sub_norm_le (period v (tau:ℂ)) (period v z)
  rw [norm_sub_rev] at hlo
  have hhi := norm_sub_norm_le (period v z) (period v (tau:ℂ))
  constructor <;> linarith

lemma period_ne_zero (tau : UpperHalfPlane) {v : Fin 2 → ℤ} (hv : v≠0) :
    period v (tau:ℂ)≠0 := by
  intro h
  have he : PeriodEisenstein318.latticeMap tau v=PeriodEisenstein318.latticeMap tau 0 := by
    apply Subtype.ext
    simpa [PeriodEisenstein318.latticeMap,period] using h
  exact hv (PeriodEisenstein318.latticeMap_injective tau he)

lemma small_periods_finite (tau : UpperHalfPlane) (r : ℝ) :
    {v : Fin 2 → ℤ | ‖period v (tau:ℂ)‖≤r}.Finite := by
  have hf : (Metric.closedBall (0 : (PeriodEisenstein318.periods tau).lattice) r).Finite :=
    isCompact_iff_finite.mp (isCompact_closedBall _ _)
  have hp := hf.preimage (PeriodEisenstein318.latticeMap_injective tau).injOn
  convert hp using 1
  ext v
  simp only [Set.mem_setOf_eq,Set.mem_preimage,Metric.mem_closedBall,dist_zero_right]
  rfl

end UniformPeriodBounds318
