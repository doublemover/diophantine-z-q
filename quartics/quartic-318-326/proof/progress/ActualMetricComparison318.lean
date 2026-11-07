module
public import ConformalCurvature318
public section
noncomputable section
namespace ActualMetricComparison318
open Filter Set CompactMetricComparison318 ConformalCurvature318
open scoped Topology
set_option maxHeartbeats 0

/-- The ordinary Laplacian depends only on the actual local coordinate germ. -/
theorem laplacian_congr {f g : ℝ × ℝ → ℝ} (he : f =ᶠ[𝓝 (0, 0)] g) :
    laplacianAtOrigin f = laplacianAtOrigin g := by
  have hx : ContinuousAt (fun t : ℝ => (t, (0 : ℝ))) 0 := by fun_prop
  have hy : ContinuousAt (fun t : ℝ => ((0 : ℝ), t)) 0 := by fun_prop
  have ex := he.comp_tendsto hx
  have ey := he.comp_tendsto hy
  unfold laplacianAtOrigin
  simpa only [Function.comp_def] using congrArg₂ (· + ·) ex.deriv.deriv_eq ey.deriv.deriv_eq

/-- Compact comparison from actual C² local metric coefficients and their
computed curvature.  The logarithmic curvature identity is derived, not supplied.
The chart ratio need only agree locally, as is true for a genuine chart germ. -/
theorem ratio_le_one {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (ratio : X → ℝ) (hcontinuous : Continuous ratio) (hpositive : ∀ x, 0 < ratio x)
    (C : ℝ) (hC : 0 < C)
    (chart : X → ℝ × ℝ → X) (chart_origin : ∀ x, chart x (0, 0) = x)
    (chart_continuous : ∀ x, ContinuousAt (chart x) (0, 0))
    (rho hyperbolic : X → ℝ × ℝ → ℝ)
    (rho_smooth : ∀ x, AxisC2 (rho x)) (hyperbolic_smooth : ∀ x, AxisC2 (hyperbolic x))
    (rho_positive : ∀ x, 0 < rho x (0, 0))
    (hyperbolic_positive : ∀ x, 0 < hyperbolic x (0, 0))
    (ratio_chart : ∀ x, (fun z => ratio (chart x z)) =ᶠ[𝓝 (0, 0)]
      (fun z => rho x z / (C * hyperbolic x z)))
    (rho_curvature : ∀ x, curvature (rho x) ≤ -1 / C)
    (hyperbolic_curvature : ∀ x, curvature (hyperbolic x) = -1) :
    ∀ x, ratio x ≤ 1 := by
  apply compact_ratio_le_one ratio hcontinuous hpositive C hC chart chart_origin chart_continuous
    (fun x => hyperbolic x (0, 0)) (fun x => curvature (rho x))
    hyperbolic_positive rho_curvature
  intro x
  have hlog : (fun z => Real.log (ratio (chart x z))) =ᶠ[𝓝 (0, 0)]
      (fun z => Real.log (rho x z / (C * hyperbolic x z))) := by
    simpa only [Function.comp_def] using (ratio_chart x).fun_comp Real.log
  rw [laplacian_congr hlog]
  rw [hyperbolic_curvature_identity (rho x) (hyperbolic x) C (rho_smooth x)
    (hyperbolic_smooth x) (rho_positive x) (hyperbolic_positive x) hC (hyperbolic_curvature x)]
  have he := (ratio_chart x).eq_of_nhds
  change ratio (chart x (0, 0)) = rho x (0, 0) / (C * hyperbolic x (0, 0)) at he
  rw [chart_origin] at he
  rw [he, mul_div_cancel₀ _ (mul_pos hC (hyperbolic_positive x)).ne']

/-- The literal local metric inequality at every point, with actual curvature
and no assumed maximum-principle or logarithmic curvature identity. -/
theorem metric_comparison {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (ratio : X → ℝ) (hcontinuous : Continuous ratio) (hpositive : ∀ x, 0 < ratio x)
    (C : ℝ) (hC : 0 < C)
    (chart : X → ℝ × ℝ → X) (chart_origin : ∀ x, chart x (0, 0) = x)
    (chart_continuous : ∀ x, ContinuousAt (chart x) (0, 0))
    (rho hyperbolic : X → ℝ × ℝ → ℝ)
    (rho_smooth : ∀ x, AxisC2 (rho x)) (hyperbolic_smooth : ∀ x, AxisC2 (hyperbolic x))
    (rho_positive : ∀ x, 0 < rho x (0, 0))
    (hyperbolic_positive : ∀ x, 0 < hyperbolic x (0, 0))
    (ratio_chart : ∀ x, (fun z => ratio (chart x z)) =ᶠ[𝓝 (0, 0)]
      (fun z => rho x z / (C * hyperbolic x z)))
    (rho_curvature : ∀ x, curvature (rho x) ≤ -1 / C)
    (hyperbolic_curvature : ∀ x, curvature (hyperbolic x) = -1) :
    ∀ x, rho x (0, 0) ≤ C * hyperbolic x (0, 0) := by
  have hb := ratio_le_one ratio hcontinuous hpositive C hC chart chart_origin chart_continuous
    rho hyperbolic rho_smooth hyperbolic_smooth rho_positive hyperbolic_positive
    ratio_chart rho_curvature hyperbolic_curvature
  intro x
  have he := (ratio_chart x).eq_of_nhds
  change ratio (chart x (0, 0)) = rho x (0, 0) / (C * hyperbolic x (0, 0)) at he
  rw [chart_origin] at he
  exact (div_le_one (mul_pos hC (hyperbolic_positive x))).mp (by simpa [he] using hb x)

end ActualMetricComparison318
#print axioms ActualMetricComparison318.laplacian_congr
#print axioms ActualMetricComparison318.ratio_le_one
#print axioms ActualMetricComparison318.metric_comparison
