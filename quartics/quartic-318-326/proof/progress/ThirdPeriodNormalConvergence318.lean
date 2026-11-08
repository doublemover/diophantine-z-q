module
public import ThirdPeriodSummands318
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public section
noncomputable section
open Filter Set
open scoped Topology
namespace ThirdPeriodNormalConvergence318
open UniformPeriodBounds318 ThirdPeriodSummands318 PeriodEisenstein318
set_option maxHeartbeats 0

@[expose] def sum (z : ℂ) : ℂ := ∑' v : Fin 2 → ℤ, summand v z

lemma sum_analyticAt (tau : UpperHalfPlane) : AnalyticAt ℂ sum (tau:ℂ) := by
  let U : Set ℂ := Metric.ball (tau:ℂ) (tau.im/2) ∩ UpperHalfPlane.upperHalfPlaneSet
  have hU : IsOpen U := Metric.isOpen_ball.inter UpperHalfPlane.isOpen_upperHalfPlaneSet
  have ht : (tau:ℂ)∈U := ⟨by simp [half_pos tau.im_pos],tau.im_pos⟩
  have hc : TendstoUniformlyOn (fun s : Finset (Fin 2 → ℤ) => fun z => ∑v∈s, summand v z)
      sum atTop U := by
    apply tendstoUniformlyOn_tsum_of_cofinite_eventually (majorant_summable tau)
    apply Filter.eventually_cofinite.mpr
    apply (small_periods_finite tau 4).subset
    intro v hv
    by_contra hn
    have hlarge : 4≤‖period v (tau:ℂ)‖ := le_of_lt (lt_of_not_ge hn)
    apply hv
    intro z hz
    exact uniform_bound tau v z (le_of_lt (by simpa [dist_eq_norm] using hz.1)) hlarge
  have hf : DifferentiableOn ℂ sum U := hc.tendstoLocallyUniformlyOn.differentiableOn
    (Filter.Eventually.of_forall (fun s => DifferentiableOn.fun_sum (fun v _ => by
      intro z hz
      exact (summand_analyticAt ⟨z,hz.2⟩ v).differentiableAt.differentiableWithinAt))) hU
  exact hf.analyticOnNhd hU (tau:ℂ) ht

lemma sum_eq (tau : UpperHalfPlane) :
    sum (tau:ℂ)=(periods tau).weierstrassPExcept 0 (1/3:ℂ) := by
  rw [PeriodPair.weierstrassPExcept,←(latticeEquiv tau).tsum_eq]
  apply tsum_congr
  intro v
  change summand v (tau:ℂ)=
    if period v (tau:ℂ)=0 then 0 else 1/((1/3:ℂ)-period v (tau:ℂ))^2-1/(period v (tau:ℂ))^2
  by_cases hv : v=0
  · simp [summand,hv,period]
  · simp [summand,hv,period_ne_zero tau hv]

lemma weierstrass_eq (tau : UpperHalfPlane) :
    (periods tau).weierstrassP (1/3:ℂ)=sum (tau:ℂ)+9 := by
  have he := (periods tau).weierstrassPExcept_add (0 : (periods tau).lattice) (1/3:ℂ)
  simp only [ZeroMemClass.coe_zero] at he
  rw [←sum_eq tau] at he
  norm_num at he
  exact he.symm

/-- Genuine wp at the actual period point 1/3 is holomorphic as the lattice varies. -/
theorem weierstrass_analyticAt (tau : UpperHalfPlane) :
    AnalyticAt ℂ (fun z => (periods (UpperHalfPlane.ofComplex z)).weierstrassP (1/3:ℂ)) (tau:ℂ) := by
  have he : (fun z => (periods (UpperHalfPlane.ofComplex z)).weierstrassP (1/3:ℂ))
      =ᶠ[𝓝 (tau:ℂ)] (fun z => sum z+9) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds tau.im_pos] with z hz
    change (periods (UpperHalfPlane.ofComplex (⟨z,hz⟩:UpperHalfPlane))).weierstrassP (1/3:ℂ)=sum z+9
    rw [UpperHalfPlane.ofComplex_apply]
    exact weierstrass_eq ⟨z,hz⟩
  exact ((sum_analyticAt tau).add analyticAt_const).congr he.symm

end ThirdPeriodNormalConvergence318
