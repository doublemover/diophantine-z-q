module
public import ActualThreeQOrders318
public section
noncomputable section
open Filter Topology
namespace ActualThreeInfinityUniformizer318
open ActualThreeQOrders318 ActualThreeQParameter318 ActualThreeQMeromorphic318
open ThreeCompactParameter318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] def unitFactor (q : ℂ) : ℂ :=
  (1+27*reciprocalInfinity q)*(1+243*reciprocalInfinity q)^3 / ActualQJ318.G q

lemma unitFactor_analytic : AnalyticAt ℂ unitFactor 0 := by
  apply AnalyticAt.div
  · exact (analyticAt_const.add (analyticAt_const.mul reciprocalInfinity_analytic)).mul
      ((analyticAt_const.add (analyticAt_const.mul reciprocalInfinity_analytic)).pow 3)
  · exact ActualQJ318.G_holomorphic.analyticOnNhd Metric.isOpen_ball 0 (by simp)
  · rw [ActualQJ318.G_zero]
    exact one_ne_zero

lemma unitFactor_zero : unitFactor 0 = 1 := by
  simp [unitFactor,reciprocalInfinity_zero,ActualQJ318.G_zero]

/-- The literal q-j normalization fixes the leading coefficient of the
reciprocal T parameter at the actual identity cusp to one. -/
theorem reciprocal_factor : reciprocalInfinity =ᶠ[𝓝 (0:ℂ)] (fun q => q*unitFactor q) := by
  apply (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    reciprocalInfinity_analytic.continuousAt (analyticAt_id.mul unitFactor_analytic).continuousAt).mp
  have hG : ∀ᶠ q in 𝓝 (0:ℂ), ActualQJ318.G q ≠ 0 := by
    apply (ActualQJ318.G_holomorphic.analyticOnNhd Metric.isOpen_ball 0 (by simp)).continuousAt.eventually_ne
    rw [ActualQJ318.G_zero]
    exact one_ne_zero
  filter_upwards [eventually_punctured 1,hG.filter_mono nhdsWithin_le_nhds] with q hq hGq
  have hT : qParameter 1 q ≠ 0 := qParameter_ne_zero 1 hq
  have hH : reciprocalInfinity q ≠ 0 := inv_ne_zero hT
  have hi : J (reciprocalInfinity q)⁻¹ =
      (1+27*reciprocalInfinity q)*(1+243*reciprocalInfinity q)^3/reciprocalInfinity q :=
    J_reciprocal _ hH
  have he := j_identity 1 hq
  simp only [ActualThreeCuspJ318.jExpression,ActualThreeCuspJ318.natWidth,
    ActualThreeCuspWidths318.width_identity,pow_one] at he
  have hinv : (reciprocalInfinity q)⁻¹ = qParameter 1 q := inv_inv _
  rw [hinv] at hi
  rw [hi] at he
  dsimp only [Pi.mul_apply,id_eq]
  unfold unitFactor
  rw [←mul_div_assoc]
  apply (eq_div_iff hGq).mpr
  have he' := (div_eq_div_iff hH hq.1).mp he
  linear_combination -he'

/-- The exact reciprocal source-cusp coordinate has derivative one, not
merely a nonzero derivative or an unspecified unit. -/
theorem reciprocalInfinity_hasDerivAt : HasDerivAt reciprocalInfinity 1 0 := by
  have hd : HasDerivAt (fun q : ℂ => q*unitFactor q) 1 0 := by
    simpa [unitFactor_zero] using! (hasDerivAt_id (0:ℂ)).mul unitFactor_analytic.differentiableAt.hasDerivAt
  exact hd.congr_of_eventuallyEq reciprocal_factor

lemma reciprocalInfinity_deriv : deriv reciprocalInfinity 0 = 1 :=
  reciprocalInfinity_hasDerivAt.deriv

end ActualThreeInfinityUniformizer318
