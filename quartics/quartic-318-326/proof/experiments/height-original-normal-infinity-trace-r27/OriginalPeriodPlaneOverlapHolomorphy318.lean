module
public import OriginalPeriodInfinityComplexAtlas318
public section
noncomputable section
namespace OriginalPeriodPlaneOverlapHolomorphy318
open OriginalPeriodPlaneOverlap318 ComplexAffineFreeTranslation318 Filter
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 2600000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
local instance : ChartedSpace ℂ (OriginalPeriodFiniteComplexAtlas318.Plane L) :=
  OriginalPeriodFiniteComplexAtlas318.chartedSpace L
local instance : ChartedSpace ℂ (InfinityPlane L) := OriginalPeriodInfinityComplexAtlas318.chartedSpace L

/-- The ACTUAL finite-to-infinity coordinate map is holomorphic on the
WHOLE original overlap for the TWO independently constructed complex atlases. -/
theorem toInfinity_holomorphic (p : OriginalPeriodFiniteComplexAtlas318.Plane L) (hp : p.val.2≠0) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (toInfinity L) p := by
  let e := OriginalPeriodFiniteComplexAtlas318.chart L p
  have hc := OriginalPeriodFiniteComplexAtlas318.chart_center L p
  have ha := OriginalPeriodFiniteComplexAtlas318.inverse_analytic L p (e p) (e.map_source hc)
  have hden : ((e.symm (e p)).val).2≠0 := by rw [e.left_inv hc];exact hp
  have hx : AnalyticAt ℂ (fun z => ((e.symm z).val).1/((e.symm z).val).2) (e p) :=
    (analyticAt_fst.comp ha).div (analyticAt_snd.comp ha) hden
  have hy : AnalyticAt ℂ (fun z => 1/((e.symm z).val).2) (e p) :=
    analyticAt_const.div (analyticAt_snd.comp ha) hden
  have hn : ∀ᶠ z in 𝓝 (e p),((e.symm z).val).2≠0 :=
    (analyticAt_snd.comp ha).continuousAt.eventually (eventually_ne_nhds hden)
  apply contMDiffAt_iff.mpr
  refine ⟨(toInfinity_continuous L p hp).continuousAt
    ((isOpen_ne (by fun_prop) continuous_const).mem_nhds hp),?_⟩
  change ContDiffWithinAt ℂ ω
    (fun z => OriginalPeriodInfinityComplexAtlas318.chart L (toInfinity L p)
      (toInfinity L (e.symm z))) _ (e p)
  rcases OriginalPeriodInfinityComplexAtlas318.chart_axis L (toInfinity L p) with haxis | haxis
  · apply (hx.congr ?_).contDiffAt.contDiffWithinAt
    filter_upwards [hn] with z hz
    rw [haxis,toInfinity_value L _ hz]
  · apply (hy.congr ?_).contDiffAt.contDiffWithinAt
    filter_upwards [hn] with z hz
    rw [haxis,toInfinity_value L _ hz]

/-- The inverse ACTUAL infinity-to-finite map is holomorphic throughout
D(v), with the original algebraic rational expressions and no atlas transport. -/
theorem toFinite_holomorphic (p : InfinityPlane L) (hp : p.val.2≠0) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (toFinite L) p := by
  let e := OriginalPeriodInfinityComplexAtlas318.chart L p
  have hc := OriginalPeriodInfinityComplexAtlas318.chart_center L p
  have ha := OriginalPeriodInfinityComplexAtlas318.inverse_analytic L p (e p) (e.map_source hc)
  have hden : ((e.symm (e p)).val).2≠0 := by rw [e.left_inv hc];exact hp
  have hx : AnalyticAt ℂ (fun z => ((e.symm z).val).1/((e.symm z).val).2) (e p) :=
    (analyticAt_fst.comp ha).div (analyticAt_snd.comp ha) hden
  have hy : AnalyticAt ℂ (fun z => 1/((e.symm z).val).2) (e p) :=
    analyticAt_const.div (analyticAt_snd.comp ha) hden
  have hn : ∀ᶠ z in 𝓝 (e p),((e.symm z).val).2≠0 :=
    (analyticAt_snd.comp ha).continuousAt.eventually (eventually_ne_nhds hden)
  apply contMDiffAt_iff.mpr
  refine ⟨(toFinite_continuous L p hp).continuousAt
    ((isOpen_ne (by fun_prop) continuous_const).mem_nhds hp),?_⟩
  change ContDiffWithinAt ℂ ω
    (fun z => OriginalPeriodFiniteComplexAtlas318.chart L (toFinite L p)
      (toFinite L (e.symm z))) _ (e p)
  rcases OriginalPeriodFiniteComplexAtlas318.chart_axis L (toFinite L p) with haxis | haxis
  · apply (hx.congr ?_).contDiffAt.contDiffWithinAt
    filter_upwards [hn] with z hz
    rw [haxis,toFinite_value L _ hz]
  · apply (hy.congr ?_).contDiffAt.contDiffWithinAt
    filter_upwards [hn] with z hz
    rw [haxis,toFinite_value L _ hz]

/-- Genuine biholomorphic gluing data on the unchanged full overlap. -/
theorem overlap_biholomorphic :
    ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (overlap L) (overlap L).source ∧
    ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (overlap L).symm (overlap L).target :=
  ⟨fun p hp => (toInfinity_holomorphic L p hp).contMDiffWithinAt,
    fun p hp => (toFinite_holomorphic L p hp).contMDiffWithinAt⟩
end OriginalPeriodPlaneOverlapHolomorphy318
