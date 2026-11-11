module
public import OriginalPeriodIndependentContinuity318
public section
noncomputable section
namespace OriginalPeriodIndependentHolomorphy318
open OriginalPeriodCompletedPointIdentification318 OriginalPeriodPlaneOverlap318
open OriginalPeriodIndependentContinuity318 OriginalPeriodNativeChartGerms318
open OriginalPeriodWeierstrassCoordinates318 ComplexAffineFreeTranslation318
open Filter Set
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 2600000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
local instance : ChartedSpace ℂ (Torus L) := ComplexLineLatticeAtlas318.chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus L) := ComplexLineLatticeAtlas318.complex_manifold L
local instance : ChartedSpace ℂ (CompletedPlane L) := OriginalPeriodCompletedComplexAtlas318.chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CompletedPlane L) := OriginalPeriodCompletedComplexAtlas318.complex_manifold L

private lemma target_chart (e : OpenPartialHomeomorph (CompletedPlane L) ℂ)
    (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (CompletedPlane L))
    (q : Torus L) (hq : originalPoint L q∈e.source)
    (hc : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (e ∘ originalPoint L) q) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (originalPoint L) q := by
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas he hq).mpr
  refine ⟨(original_continuous L).continuousAt.continuousWithinAt,?_⟩
  change ContMDiffWithinAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (e ∘ originalPoint L) Set.univ q
  exact hc.contMDiffWithinAt

/-- All actual finite points are holomorphic for the independent global
atlas. The chosen target chart can use either original x or native y. -/
theorem finite_holomorphic (q : Torus L) (hq : q≠0) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (originalPoint L) q := by
  let p:=originalFinite L ⟨q,hq⟩
  let e:=OriginalPeriodCompletedComplexAtlas318.finiteChart L p
  have he:e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (CompletedPlane L) :=
    IsManifold.subset_maximalAtlas ⟨Sum.inl p,rfl⟩
  have hp:originalPoint L q∈e.source := by
    rw [original_nonzero L q hq]
    exact ⟨p,OriginalPeriodFiniteComplexAtlas318.chart_center L p,rfl⟩
  apply target_chart L e he q hp
  rcases OriginalPeriodFiniteComplexAtlas318.chart_axis L p with ha | ha
  · apply (OriginalPeriodWeierstrassHolomorphy318.x_holomorphicAt L q hq).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hq] with r hr
    change e (originalPoint L r)=x L r
    rw [original_nonzero L r hr]
    change OriginalPeriodCompletedComplexAtlas318.finiteChart L p
      (finiteChart L (originalFinite L ⟨r,hr⟩))=x L r
    rw [OriginalPeriodCompletedComplexAtlas318.finite_apply,ha,original_coordinates]
  · apply ((OriginalPeriodWeierstrassHolomorphy318.y_holomorphicAt L q hq).div_const 2).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hq] with r hr
    change e (originalPoint L r)=y L r/2
    rw [original_nonzero L r hr]
    change OriginalPeriodCompletedComplexAtlas318.finiteChart L p
      (finiteChart L (originalFinite L ⟨r,hr⟩))=y L r/2
    rw [OriginalPeriodCompletedComplexAtlas318.finite_apply,ha,original_coordinates]

/-- Genuine holomorphy THROUGH the original pole in the independent
infinity target atlas, using the full native U,V identity. -/
theorem pole_holomorphic :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (originalPoint L) (0:Torus L) := by
  let e:=OriginalPeriodCompletedComplexAtlas318.infinityChart L (origin L)
  have he:e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (CompletedPlane L) :=
    IsManifold.subset_maximalAtlas ⟨Sum.inr (origin L),rfl⟩
  have hp:originalPoint L 0∈e.source := by
    rw [original_zero]
    exact ⟨origin L,OriginalPeriodInfinityComplexAtlas318.chart_center L (origin L),rfl⟩
  apply target_chart L e he 0 hp
  have hh:=OriginalPeriodNativeChartGerms318.holomorphic L
  rcases OriginalPeriodInfinityComplexAtlas318.chart_axis L (origin L) with ha | ha
  · apply hh.1.congr_of_eventuallyEq
    filter_upwards [whole_pole_identity L,infinity_equation L] with r hr heq
    change e (originalPoint L r)=nativeU L r
    rw [hr]
    change OriginalPeriodCompletedComplexAtlas318.infinityChart L (origin L)
      (infinityChart L (infinityLocal L r))=nativeU L r
    rw [OriginalPeriodCompletedComplexAtlas318.infinity_apply,ha,infinityLocal_value L r heq]
  · apply hh.2.congr_of_eventuallyEq
    filter_upwards [whole_pole_identity L,infinity_equation L] with r hr heq
    change e (originalPoint L r)=nativeV L r
    rw [hr]
    change OriginalPeriodCompletedComplexAtlas318.infinityChart L (origin L)
      (infinityChart L (infinityLocal L r))=nativeV L r
    rw [OriginalPeriodCompletedComplexAtlas318.infinity_apply,ha,infinityLocal_value L r heq]

/-- The SAME original all-scheme-point bijection is globally holomorphic
into the independently constructed completed polynomial complex curve. -/
theorem original_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (originalPoint L) := by
  intro q
  by_cases hq:q=0
  · subst q
    exact pole_holomorphic L
  · exact finite_holomorphic L q hq
end OriginalPeriodIndependentHolomorphy318
