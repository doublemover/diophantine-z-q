module
public import HolomorphicQuotientJ318
public import Mathlib.Topology.Algebra.Order.Field
public section
noncomputable section
open UpperHalfPlane Function Filter Topology QuotientJ318
open scoped Manifold ContDiff
namespace ActualJCusp318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The actual normalized Laurent leading term is one. -/
theorem qj_tendsto_one : Tendsto
    (fun tau:UpperHalfPlane => Periodic.qParam 1 tau * ActualQJ318.jInvariant tau)
    atImInfty (𝓝 1) := by
  have hg := (ActualQJ318.G_differentiableAt 0 (by simp)).continuousAt.tendsto
  rw [ActualQJ318.G_zero] at hg
  simpa only [Function.comp_def,ActualQJ318.G_qParam] using
    hg.comp (qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1))

/-- In particular the actual analytic j-function is not constant. -/
theorem j_not_constant (c:ℂ) : ¬ ∀ tau:UpperHalfPlane, ActualQJ318.jInvariant tau=c := by
  intro hc
  have hz : Tendsto (fun tau:UpperHalfPlane =>
      Periodic.qParam 1 tau * ActualQJ318.jInvariant tau) atImInfty (𝓝 0) := by
    simp only [hc]
    simpa using (qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1)).mul_const c
  exact zero_ne_one (tendsto_nhds_unique hz qj_tendsto_one)

theorem jMap_not_constant (N:ℕ) (c:ℂ) : ¬ ∀ q, jMap N q=c := by
  intro hc
  exact j_not_constant c (fun tau => hc (GammaOneAtlas318.quotientMap N tau))

/-- The actual reciprocal-j germ in the cusp parameter, filled in at zero. -/
@[expose] def reciprocalGerm (q:ℂ) : ℂ := q / ActualQJ318.G q

@[simp] theorem reciprocalGerm_zero : reciprocalGerm 0=0 := by simp [reciprocalGerm]

/-- The filled reciprocal germ is genuinely holomorphic and has derivative one.
This certifies a simple pole of j at this cusp parameter. -/
theorem reciprocalGerm_hasDerivAt : HasDerivAt reciprocalGerm 1 0 := by
  have hg := (ActualQJ318.G_differentiableAt 0 (by simp)).hasDerivAt
  simpa [reciprocalGerm,ActualQJ318.G_zero] using!
    (hasDerivAt_id (0:ℂ)).div hg (by rw [ActualQJ318.G_zero];exact one_ne_zero)

theorem reciprocalGerm_analytic : AnalyticAt ℂ reciprocalGerm 0 := by
  have hg : AnalyticAt ℂ ActualQJ318.G 0 :=
    ActualQJ318.G_holomorphic.analyticOnNhd Metric.isOpen_ball 0 (by simp)
  exact analyticAt_id.div hg (by rw [ActualQJ318.G_zero];exact one_ne_zero)

/-- Exact reciprocal-j identity at every genuine upper-half-plane parameter;
the totalized divisions even make the identity true at zeros of j. -/
theorem reciprocalGerm_qParam (tau:UpperHalfPlane) :
    reciprocalGerm (Periodic.qParam 1 tau)=(ActualQJ318.jInvariant tau)⁻¹ := by
  rw [reciprocalGerm,ActualQJ318.G_qParam]
  field_simp [Periodic.qParam_ne_zero]

/-- The magnitude of the genuine j-function diverges at the actual cusp filter. -/
theorem j_norm_tendsto_atTop : Tendsto (fun tau:UpperHalfPlane =>
    ‖ActualQJ318.jInvariant tau‖) atImInfty atTop := by
  have hq : Tendsto (fun tau:UpperHalfPlane => ‖Periodic.qParam 1 tau‖)
      atImInfty (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun tau => ?_)⟩
    · simpa using (qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1)).norm
    · exact norm_pos_iff.mpr (Periodic.qParam_ne_zero _)
  have hlead : Tendsto (fun tau:UpperHalfPlane =>
      ‖Periodic.qParam 1 tau‖ * ‖ActualQJ318.jInvariant tau‖) atImInfty (𝓝 1) := by
    simpa only [norm_mul,norm_one] using qj_tendsto_one.norm
  have h := Filter.Tendsto.pos_mul_atTop (by norm_num : (0:ℝ)<1) hlead
    hq.inv_tendsto_nhdsGT_zero
  convert h using 1
  ext tau
  dsimp
  field_simp [norm_ne_zero_iff.mpr (Periodic.qParam_ne_zero _)]

/-- The actual descended map is unbounded, not merely a formally named function. -/
theorem jMap_unbounded (N:ℕ) (M:ℝ) : ∃q, M < ‖jMap N q‖ := by
  obtain ⟨tau,htau⟩ := (j_norm_tendsto_atTop.eventually_gt_atTop M).exists
  exact ⟨GammaOneAtlas318.quotientMap N tau,htau⟩

end ActualJCusp318
