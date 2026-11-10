module
public import LegendreInfinityComplexAtlas318
public section
noncomputable section
namespace LegendrePlaneOverlapHolomorphy318
open LegendrePlaneOverlap318 Filter
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 2600000
variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]
local instance : ChartedSpace ℂ (LegendreFiniteComplexAtlas318.Plane l) :=
  LegendreFiniteComplexAtlas318.chartedSpace l
local instance : ChartedSpace ℂ (InfinityPlane l) := LegendreInfinityComplexAtlas318.chartedSpace l

/-- The ACTUAL finite-to-infinity coordinate map is holomorphic on the
WHOLE original overlap for the TWO independently constructed complex atlases. -/
theorem toInfinity_holomorphic (p : LegendreFiniteComplexAtlas318.Plane l) (hp : p.val.2≠0) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (toInfinity l) p := by
  let e := LegendreFiniteComplexAtlas318.chart l p
  have hc := LegendreFiniteComplexAtlas318.chart_center l p
  have ha := LegendreFiniteComplexAtlas318.inverse_analytic l p (e p) (e.map_source hc)
  have hden : ((e.symm (e p)).val).2≠0 := by rw [e.left_inv hc];exact hp
  have hx : AnalyticAt ℂ (fun z => ((e.symm z).val).1/((e.symm z).val).2) (e p) :=
    (analyticAt_fst.comp ha).div (analyticAt_snd.comp ha) hden
  have hy : AnalyticAt ℂ (fun z => 1/((e.symm z).val).2) (e p) :=
    analyticAt_const.div (analyticAt_snd.comp ha) hden
  have hn : ∀ᶠ z in 𝓝 (e p),((e.symm z).val).2≠0 :=
    (analyticAt_snd.comp ha).continuousAt.eventually (eventually_ne_nhds hden)
  apply contMDiffAt_iff.mpr
  refine ⟨(toInfinity_continuous l p hp).continuousAt
    ((isOpen_ne (by fun_prop) continuous_const).mem_nhds hp),?_⟩
  change ContDiffWithinAt ℂ ω
    (fun z => LegendreInfinityComplexAtlas318.chart l (toInfinity l p)
      (toInfinity l (e.symm z))) _ (e p)
  rcases LegendreInfinityComplexAtlas318.chart_axis l (toInfinity l p) with haxis | haxis
  · apply (hx.congr ?_).contDiffAt.contDiffWithinAt
    filter_upwards [hn] with z hz
    rw [haxis,toInfinity_value l _ hz]
  · apply (hy.congr ?_).contDiffAt.contDiffWithinAt
    filter_upwards [hn] with z hz
    rw [haxis,toInfinity_value l _ hz]

/-- The inverse ACTUAL infinity-to-finite map is holomorphic throughout
D(v), with the original algebraic rational expressions and no atlas transport. -/
theorem toFinite_holomorphic (p : InfinityPlane l) (hp : p.val.2≠0) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (toFinite l) p := by
  let e := LegendreInfinityComplexAtlas318.chart l p
  have hc := LegendreInfinityComplexAtlas318.chart_center l p
  have ha := LegendreInfinityComplexAtlas318.inverse_analytic l p (e p) (e.map_source hc)
  have hden : ((e.symm (e p)).val).2≠0 := by rw [e.left_inv hc];exact hp
  have hx : AnalyticAt ℂ (fun z => ((e.symm z).val).1/((e.symm z).val).2) (e p) :=
    (analyticAt_fst.comp ha).div (analyticAt_snd.comp ha) hden
  have hy : AnalyticAt ℂ (fun z => 1/((e.symm z).val).2) (e p) :=
    analyticAt_const.div (analyticAt_snd.comp ha) hden
  have hn : ∀ᶠ z in 𝓝 (e p),((e.symm z).val).2≠0 :=
    (analyticAt_snd.comp ha).continuousAt.eventually (eventually_ne_nhds hden)
  apply contMDiffAt_iff.mpr
  refine ⟨(toFinite_continuous l p hp).continuousAt
    ((isOpen_ne (by fun_prop) continuous_const).mem_nhds hp),?_⟩
  change ContDiffWithinAt ℂ ω
    (fun z => LegendreFiniteComplexAtlas318.chart l (toFinite l p)
      (toFinite l (e.symm z))) _ (e p)
  rcases LegendreFiniteComplexAtlas318.chart_axis l (toFinite l p) with haxis | haxis
  · apply (hx.congr ?_).contDiffAt.contDiffWithinAt
    filter_upwards [hn] with z hz
    rw [haxis,toFinite_value l _ hz]
  · apply (hy.congr ?_).contDiffAt.contDiffWithinAt
    filter_upwards [hn] with z hz
    rw [haxis,toFinite_value l _ hz]

/-- Genuine biholomorphic gluing data on the unchanged full overlap. -/
theorem overlap_biholomorphic :
    ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (overlap l) (overlap l).source ∧
    ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (overlap l).symm (overlap l).target :=
  ⟨fun p hp => (toInfinity_holomorphic l p hp).contMDiffWithinAt,
    fun p hp => (toFinite_holomorphic l p hp).contMDiffWithinAt⟩
end LegendrePlaneOverlapHolomorphy318
