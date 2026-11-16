module
public import LiteralContactGlobalMetricRatio318
public import UniformizingSectionBounds318
public section
noncomputable section
namespace LiteralContactUniformizingData318
open Set Filter FourRootNormalizedPointCharts318 LiteralMetricExtension318
open LiteralContactMetricCharts318 LiteralChartMetricFunctions318 LiteralContactGlobalMetricRatio318
open PELUnlevelledComplexBase318 MobiusPoincarePullback318
open scoped Topology Manifold ContDiff
local instance : TopologicalSpace (Completed contacts) := FourRootGluedTopology318.topology contacts
local instance : ChartedSpace ℂ (Completed contacts) := FourRootCompletedComplexAtlas318.chartedSpace contacts contacts_injective
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed contacts) := FourRootCompletedComplexAtlas318.complex_manifold contacts contacts_injective
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold
variable (H : UnlevelledBase ≃ₜ Completed contacts)
  (hH : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H)
  (hI : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm)

@[expose] def param (p : Completed contacts) (z : ℂ) : Completed contacts :=
  (data p).chart.symm ((data p).chart p+z)
lemma param_zero (p : Completed contacts) : param p 0=p := by
  rw [param,add_zero,(data p).chart.left_inv (data p).mem]
@[expose] def lift (p : Completed contacts) : ℂ → ℂ :=
  (OriginalUniformizedCurveAtlas318.exists_uniformizer_with_metric H hH hI
    (data p).chart p (data p).mem (data p).maximal).choose
lemma lift_analytic (p : Completed contacts) : AnalyticAt ℂ (lift H hH hI p) 0 :=
  (OriginalUniformizedCurveAtlas318.exists_uniformizer_with_metric H hH hI
    (data p).chart p (data p).mem (data p).maximal).choose_spec.1
lemma lift_upper (p : Completed contacts) : 0<(lift H hH hI p 0).im :=
  (OriginalUniformizedCurveAtlas318.exists_uniformizer_with_metric H hH hI
    (data p).chart p (data p).mem (data p).maximal).choose_spec.2.1
lemma lift_noncritical (p : Completed contacts) : deriv (lift H hH hI p) 0≠0 :=
  (OriginalUniformizedCurveAtlas318.exists_uniformizer_with_metric H hH hI
    (data p).chart p (data p).mem (data p).maximal).choose_spec.2.2.1
lemma lift_metric (p : Completed contacts) :
    ∀ᶠ z in 𝓝 (0:ℂ),OriginalUniformizedCurveAtlas318.coefficient H (data p).chart (param p z)=
      density (lift H hH hI p) z :=
  (OriginalUniformizedCurveAtlas318.exists_uniformizer_with_metric H hH hI
    (data p).chart p (data p).mem (data p).maximal).choose_spec.2.2.2.2

lemma ratio_uniformizer (p : Completed contacts) :
    ∀ᶠ z in 𝓝 (0:ℂ),ratio H (param p z)=
      value (data p).kind z/(12540153541944538512*density (lift H hH hI p) z) := by
  filter_upwards [LiteralContactGlobalMetricRatio318.ratio_chart H hH hI p,lift_metric H hH hI p] with z hz hm
  exact hz.trans (by rw [hm])
lemma density_positive (p : Completed contacts) : 0<density (lift H hH hI p) 0 :=
  div_pos (pow_pos (norm_pos_iff.mpr (lift_noncritical H hH hI p)) 2)
    (pow_pos (lift_upper H hH hI p) 2)
lemma density_continuous (p : Completed contacts) : ContinuousAt (density (lift H hH hI p)) 0 := by
  have hf := lift_analytic H hH hI p
  exact (hf.deriv.continuousAt.norm.pow 2).div
    ((Complex.continuous_im.continuousAt.comp hf.continuousAt).pow 2)
      (pow_ne_zero 2 (lift_upper H hH hI p).ne')

include hH hI in
/-- Genuine continuity of the globally selected source/Poincare ratio.
It is proved from the actual local metric identity, not from continuous
chart choices or an assumed global metric realization. -/
theorem ratio_continuous : Continuous (ratio H) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let E := (data p).chart
  let L : ℂ → ℝ := fun z => value (data p).kind z /
    (12540153541944538512*density (lift H hH hI p) z)
  have hL : ContinuousAt L 0 := (value_continuous (data p).kind).div
    (continuousAt_const.mul (density_continuous H hH hI p))
    (mul_ne_zero (by norm_num) (density_positive H hH hI p).ne')
  have hcoord : ContinuousAt (fun q => E q-E p) p :=
    (E.continuousAt (data p).mem).sub continuousAt_const
  have ht : Tendsto (fun q => E q-E p) (𝓝 p) (𝓝 (0:ℂ)) := by
    simpa only [sub_self] using hcoord
  have hcomp : ContinuousAt (fun q => L (E q-E p)) p :=
    (show ContinuousAt L (E p-E p) by simpa only [sub_self] using hL).comp hcoord
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [ht.eventually (ratio_uniformizer H hH hI p),E.open_source.mem_nhds (data p).mem]
    with q hq hqs
  have hpq : param p (E q-E p)=q := by
    change E.symm (E p+(E q-E p))=q
    rw [show E p+(E q-E p)=E q by ring,E.left_inv hqs]
  exact hpq ▸ hq

/-- All fields of the quantitative uniformizing-data interface are now
CONSTRUCTED on the literal completed curve from one actual original
biholomorphism. No chart, global ratio, curvature, gradient or section
estimate is supplied as an additional premise. -/
@[expose] def uniformizingData : UniformizingSectionBounds318.Data (Completed contacts) where
  kind p := (data p).kind
  ratio := ratio H
  ratio_continuous := ratio_continuous H hH hI
  ratio_positive := ratio_positive H hH hI
  chart p w := param p (QuadraticOrigin318.complexCoord w)
  chart_origin p := by simpa [QuadraticOrigin318.complexCoord] using param_zero p
  chart_continuous p := by
    have hc : ContinuousAt (fun w : ℝ×ℝ => (data p).chart p+QuadraticOrigin318.complexCoord w) (0,0) := by
      unfold QuadraticOrigin318.complexCoord
      fun_prop
    exact ((data p).chart.continuousAt_symm
      (by simpa [QuadraticOrigin318.complexCoord] using (data p).chart.map_source (data p).mem)).comp hc
  uniformizer := lift H hH hI
  analytic := lift_analytic H hH hI
  upper := lift_upper H hH hI
  noncritical := lift_noncritical H hH hI
  ratio_chart p := by
    have hc : ContinuousAt QuadraticOrigin318.complexCoord (0,0) := by
      unfold QuadraticOrigin318.complexCoord
      fun_prop
    have ht : Tendsto QuadraticOrigin318.complexCoord (𝓝 (0,0)) (𝓝 (0:ℂ)) := by
      simpa [QuadraticOrigin318.complexCoord] using hc
    filter_upwards [ht.eventually (ratio_uniformizer H hH hI p)] with w hw
    simpa only [value_real,density_eq_coefficient] using hw
end LiteralContactUniformizingData318
