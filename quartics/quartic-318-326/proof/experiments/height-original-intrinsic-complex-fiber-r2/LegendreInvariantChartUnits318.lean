module
public import LegendreInvariantAnalytic318
public section
noncomputable section
namespace LegendreInvariantChartUnits318
open Set Filter
open scoped Topology
open LegendreInvariantTangent318 LegendreInvariantAnalytic318
open LegendreIndependentGraphs318
variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]

@[expose] def finiteX (p : LegendreFiniteComplexAtlas318.Plane l) (z : ℂ) : ℂ :=
  ((LegendreFiniteComplexAtlas318.chart l p).symm z).val.1
@[expose] def finiteY (p : LegendreFiniteComplexAtlas318.Plane l) (z : ℂ) : ℂ :=
  ((LegendreFiniteComplexAtlas318.chart l p).symm z).val.2
@[expose] def infiniteU (p : LegendrePlaneOverlap318.InfinityPlane l) (z : ℂ) : ℂ :=
  ((LegendreInfinityComplexAtlas318.chart l p).symm z).val.1
@[expose] def infiniteV (p : LegendrePlaneOverlap318.InfinityPlane l) (z : ℂ) : ℂ :=
  ((LegendreInfinityComplexAtlas318.chart l p).symm z).val.2
@[expose] def finiteForm (p : LegendreFiniteComplexAtlas318.Plane l) : ℂ→ℂ :=
  finiteCoefficient l (finiteX l p) (finiteY l p)
@[expose] def infinityForm (p : LegendrePlaneOverlap318.InfinityPlane l) : ℂ→ℂ :=
  infinityCoefficient l (infiniteU l p) (infiniteV l p)

lemma finite_coordinates (p : LegendreFiniteComplexAtlas318.Plane l) :
    AnalyticOnNhd ℂ (finiteX l p) (LegendreFiniteComplexAtlas318.chart l p).target ∧
    AnalyticOnNhd ℂ (finiteY l p) (LegendreFiniteComplexAtlas318.chart l p).target :=
  ⟨fun z hz=>analyticAt_fst.comp (LegendreFiniteComplexAtlas318.inverse_analytic l p z hz),
   fun z hz=>analyticAt_snd.comp (LegendreFiniteComplexAtlas318.inverse_analytic l p z hz)⟩
lemma infinite_coordinates (p : LegendrePlaneOverlap318.InfinityPlane l) :
    AnalyticOnNhd ℂ (infiniteU l p) (LegendreInfinityComplexAtlas318.chart l p).target ∧
    AnalyticOnNhd ℂ (infiniteV l p) (LegendreInfinityComplexAtlas318.chart l p).target :=
  ⟨fun z hz=>analyticAt_fst.comp (LegendreInfinityComplexAtlas318.inverse_analytic l p z hz),
   fun z hz=>analyticAt_snd.comp (LegendreInfinityComplexAtlas318.inverse_analytic l p z hz)⟩

theorem finiteForm_analytic (p : LegendreFiniteComplexAtlas318.Plane l) :
    AnalyticOnNhd ℂ (finiteForm l p) (LegendreFiniteComplexAtlas318.chart l p).target :=
  LegendreInvariantAnalytic318.finite_analytic l _ _ _
    (LegendreFiniteComplexAtlas318.chart l p).open_target
    (finite_coordinates l p).1 (finite_coordinates l p).2
    (fun z _=>((LegendreFiniteComplexAtlas318.chart l p).symm z).property)
theorem infinityForm_analytic (p : LegendrePlaneOverlap318.InfinityPlane l) :
    AnalyticOnNhd ℂ (infinityForm l p) (LegendreInfinityComplexAtlas318.chart l p).target :=
  LegendreInvariantAnalytic318.infinity_analytic l _ _ _
    (LegendreInfinityComplexAtlas318.chart l p).open_target
    (infinite_coordinates l p).1 (infinite_coordinates l p).2
    (fun z _=>((LegendreInfinityComplexAtlas318.chart l p).symm z).property)

/-- At every actual inverse chart one coordinate derivative is exactly1.
Thus nonvanishing comes from the actual chart inverse, not a supplied
immersivity or a chosen nonzero tangent hypothesis. -/
lemma finite_axis_derivative (p : LegendreFiniteComplexAtlas318.Plane l) (z : ℂ)
    (hz : z∈(LegendreFiniteComplexAtlas318.chart l p).target) :
    deriv (finiteX l p) z=1 ∨ deriv (finiteY l p) z=1 := by
  rcases LegendreFiniteComplexAtlas318.chart_axis l p with hx|hy
  · left
    apply HasDerivAt.deriv
    apply (hasDerivAt_id z).congr_of_eventuallyEq
    filter_upwards [(LegendreFiniteComplexAtlas318.chart l p).open_target.mem_nhds hz] with w hw
    exact (hx _).symm.trans ((LegendreFiniteComplexAtlas318.chart l p).right_inv hw)
  · right
    apply HasDerivAt.deriv
    apply (hasDerivAt_id z).congr_of_eventuallyEq
    filter_upwards [(LegendreFiniteComplexAtlas318.chart l p).open_target.mem_nhds hz] with w hw
    exact (hy _).symm.trans ((LegendreFiniteComplexAtlas318.chart l p).right_inv hw)
lemma infinite_axis_derivative (p : LegendrePlaneOverlap318.InfinityPlane l) (z : ℂ)
    (hz : z∈(LegendreInfinityComplexAtlas318.chart l p).target) :
    deriv (infiniteU l p) z=1 ∨ deriv (infiniteV l p) z=1 := by
  rcases LegendreInfinityComplexAtlas318.chart_axis l p with hu|hv
  · left
    apply HasDerivAt.deriv
    apply (hasDerivAt_id z).congr_of_eventuallyEq
    filter_upwards [(LegendreInfinityComplexAtlas318.chart l p).open_target.mem_nhds hz] with w hw
    exact (hu _).symm.trans ((LegendreInfinityComplexAtlas318.chart l p).right_inv hw)
  · right
    apply HasDerivAt.deriv
    apply (hasDerivAt_id z).congr_of_eventuallyEq
    filter_upwards [(LegendreInfinityComplexAtlas318.chart l p).open_target.mem_nhds hz] with w hw
    exact (hv _).symm.trans ((LegendreInfinityComplexAtlas318.chart l p).right_inv hw)

theorem finiteForm_ne_zero (p : LegendreFiniteComplexAtlas318.Plane l) (z : ℂ)
    (hz : z∈(LegendreFiniteComplexAtlas318.chart l p).target) : finiteForm l p z≠0 := by
  have ht:=finite_derivative l (finiteX l p) (finiteY l p)
    ((finite_coordinates l p).1 z hz).differentiableAt
    ((finite_coordinates l p).2 z hz).differentiableAt
    (Filter.Eventually.of_forall (fun w=>((LegendreFiniteComplexAtlas318.chart l p).symm w).property))
  intro hzero
  have h:=(finite_kernel l ((LegendreFiniteComplexAtlas318.chart l p).symm z) _ _ ht).mp hzero
  rcases finite_axis_derivative l p z hz with hx|hy
  · exact zero_ne_one (h.1.symm.trans hx)
  · exact zero_ne_one (h.2.symm.trans hy)
theorem infinityForm_ne_zero (p : LegendrePlaneOverlap318.InfinityPlane l) (z : ℂ)
    (hz : z∈(LegendreInfinityComplexAtlas318.chart l p).target) : infinityForm l p z≠0 := by
  have ht:=infinity_derivative l (infiniteU l p) (infiniteV l p)
    ((infinite_coordinates l p).1 z hz).differentiableAt
    ((infinite_coordinates l p).2 z hz).differentiableAt
    (Filter.Eventually.of_forall (fun w=>((LegendreInfinityComplexAtlas318.chart l p).symm w).property))
  intro hzero
  have h:=(infinity_kernel l ((LegendreInfinityComplexAtlas318.chart l p).symm z) _ _ ht).mp hzero
  rcases infinite_axis_derivative l p z hz with hu|hv
  · exact zero_ne_one (h.1.symm.trans hu)
  · exact zero_ne_one (h.2.symm.trans hv)
end LegendreInvariantChartUnits318
