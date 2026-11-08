module
public import ScaledCoordinateGerm318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace LinearScalingGerm318
open PeriodEisenstein318 LatticeInvariants318 InfinityAnalyticChart318 ScaledCoordinateGerm318
set_option maxHeartbeats 0

lemma deriv_xCoord (tau : UpperHalfPlane) (z : ℂ) :
    deriv (xCoord tau) z=2*(2*(Real.pi:ℂ))*yCoord tau z := by
  have hk : 2*(Real.pi:ℂ)≠0 := mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  unfold xCoord yCoord
  rw [deriv_div_const,(periods tau).deriv_weierstrassP]
  field_simp
  <;> ring

lemma hasDerivAt_xCoord (tau : UpperHalfPlane) (z : ℂ) (hz : z ∉ (periods tau).lattice) :
    HasDerivAt (xCoord tau) (2*(2*(Real.pi:ℂ))*yCoord tau z) z := by
  simpa only [deriv_xCoord] using
    (FiniteAnalyticCharts318.xCoord_analytic tau z hz).differentiableAt.hasDerivAt

lemma regular_eventually (tau : UpperHalfPlane) :
    ∀ᶠ z in 𝓝[≠] (0:ℂ), z ∉ (periods tau).lattice := by
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
    ((periods tau).compl_lattice_sdiff_singleton_mem_nhds 0)] with z hz hn
  simp only [mem_compl_iff,Set.mem_sdiff,SetLike.mem_coe,mem_singleton_iff] at hz hn ⊢
  aesop

lemma cancel_derivative (u : ℂˣ) (k y d : ℂ) (hk : k≠0) (hy : y≠0)
    (he : (2*k*((u:ℂ)^3*y))*d=(u:ℂ)^2*(2*k*y)) : d=(u:ℂ)⁻¹ := by
  have hu : (u:ℂ)≠0 := Units.ne_zero u
  have hc : (u:ℂ)^3*(2*k*y)≠0 := by
    exact mul_ne_zero (pow_ne_zero 3 hu)
      (mul_ne_zero (mul_ne_zero (by norm_num) hk) hy)
  apply mul_left_cancel₀ hc
  calc
    ((u:ℂ)^3*(2*k*y))*d=(u:ℂ)^2*(2*k*y) := by linear_combination he
    _=((u:ℂ)^3*(2*k*y))*(u:ℂ)⁻¹ := by field_simp <;> ring

lemma linear_of_derivative_germ {w : ℂ → ℂ} {a : ℂ} (hw : AnalyticAt ℂ w 0)
    (hw0 : w 0=0) (hd : ∀ᶠ z in 𝓝 (0:ℂ), deriv w z=a) :
    w =ᶠ[𝓝 0] (fun z => a*z) := by
  have he := hw.eventually_analyticAt.and hd
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  have hdiff : DifferentiableOn ℂ w (Metric.ball (0:ℂ) r) := by
    intro z hz
    exact ((hball hz).1).differentiableAt.differentiableWithinAt
  have hlinear : DifferentiableOn ℂ (fun z : ℂ => a*z) (Metric.ball (0:ℂ) r) := by fun_prop
  have heq := Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball (0:ℂ) r).isPreconnected
    hdiff hlinear (fun z hz => by rw [(hball hz).2]; simp)
    (Metric.mem_ball_self hr) (by simp [hw0])
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr] with z hz
  exact heq hz

/-- The actual local lift of a short-model scaling is linear. This uses
both genuine Weierstrass coordinates and their derivative, not only the
algebraic coefficient identities or a chosen root labeling. -/
theorem coordinate_lift_linear (tau sigma : UpperHalfPlane) (u : ℂˣ)
    (w : ℂ → ℂ) (hw : AnalyticAt ℂ w 0) (hw0 : w 0=0)
    (hD : HasDerivAt w (u:ℂ)⁻¹ 0)
    (hx : (fun z => xCoord sigma (w z)) =ᶠ[𝓝 0] (fun z => (u:ℂ)^2*xCoord tau z))
    (hy : (fun z => yCoord sigma (w z)) =ᶠ[𝓝 0] (fun z => (u:ℂ)^3*yCoord tau z)) :
    w =ᶠ[𝓝 0] (fun z => (u:ℂ)⁻¹*z) := by
  have hwt := tendsto_puncture hw hw0 hD (inv_ne_zero (Units.ne_zero u))
  have hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), deriv w z=(u:ℂ)⁻¹ := by
    filter_upwards [regular_eventually tau,hwt.eventually (regular_eventually sigma),
      coordinates_eventually tau,mem_nhdsWithin_of_mem_nhds hw.eventually_analyticAt,
      mem_nhdsWithin_of_mem_nhds hx.eventuallyEq_nhds,
      mem_nhdsWithin_of_mem_nhds hy] with z hzt hzs hcoord hwz hxz hyz
    have hl := (hasDerivAt_xCoord sigma (w z) hzs).comp z hwz.differentiableAt.hasDerivAt
    have hr := (hasDerivAt_xCoord tau z hzt).const_mul ((u:ℂ)^2)
    have he := hl.unique (hr.congr_of_eventuallyEq hxz)
    rw [hyz] at he
    exact cancel_derivative u (2*(Real.pi:ℂ)) (yCoord tau z) (deriv w z)
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hcoord.1 he
  apply linear_of_derivative_germ hw hw0
  filter_upwards [eventually_nhdsWithin_iff.mp hd] with z hz
  by_cases hz0 : z=0
  · simpa only [hz0] using hD.deriv
  · exact hz (by simpa using hz0)

/-- Exact linear coordinate-scaling germs for the genuine period functions. -/
theorem linear_coordinate_germs (tau sigma : UpperHalfPlane) (u : ℂˣ)
    (h4 : (ModularWeierstrass318.curve sigma).a₄=(u:ℂ)^4*(ModularWeierstrass318.curve tau).a₄)
    (h6 : (ModularWeierstrass318.curve sigma).a₆=(u:ℂ)^6*(ModularWeierstrass318.curve tau).a₆) :
    (fun z => xCoord sigma ((u:ℂ)⁻¹*z)) =ᶠ[𝓝 0] (fun z => (u:ℂ)^2*xCoord tau z) ∧
    (fun z => yCoord sigma ((u:ℂ)⁻¹*z)) =ᶠ[𝓝 0] (fun z => (u:ℂ)^3*yCoord tau z) := by
  obtain ⟨w,hw,hw0,hD,hx,hy⟩ := exists_coordinate_germ tau sigma u h4 h6
  have hl := coordinate_lift_linear tau sigma u w hw hw0 hD hx hy
  constructor
  · filter_upwards [hl,hx] with z hz he
    simpa only [hz] using he
  · filter_upwards [hl,hy] with z hz he
    simpa only [hz] using he

end LinearScalingGerm318
