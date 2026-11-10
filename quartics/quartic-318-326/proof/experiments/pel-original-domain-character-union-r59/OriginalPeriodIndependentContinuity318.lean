module
public import OriginalPeriodCompletedPointIdentification318
public section
noncomputable section
namespace OriginalPeriodIndependentContinuity318
open OriginalPeriodCompletedPointIdentification318 OriginalPeriodPlaneOverlap318
open OriginalPeriodIndependentGraphs318 OriginalPeriodNativeChartGerms318
open OriginalPeriodWeierstrassCoordinates318 ComplexAffineFreeTranslation318
open OriginalPeriodFiniteComplexAtlas318 Filter Set
open scoped Topology Manifold ContDiff
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
local instance : ChartedSpace ℂ (Torus L) := ComplexLineLatticeAtlas318.chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus L) := ComplexLineLatticeAtlas318.complex_manifold L

@[expose] def finiteLocal (q : Torus L) : Plane L :=
  if hq:q≠0 then originalFinite L ⟨q,hq⟩ else fallback L
lemma finiteLocal_value (q : Torus L) (hq : q≠0) :
    (finiteLocal L q).val=(x L q,y L q/2) := by
  rw [finiteLocal,dif_pos hq]
  exact original_coordinates L ⟨q,hq⟩
lemma finiteLocal_continuous (q : Torus L) (hq : q≠0) : ContinuousAt (finiteLocal L) q := by
  apply tendsto_subtype_rng.mpr
  have hx := (OriginalPeriodWeierstrassHolomorphy318.x_holomorphicAt L q hq).continuousAt
  have hy := (OriginalPeriodWeierstrassHolomorphy318.y_holomorphicAt L q hq).continuousAt.div_const 2
  apply (hx.prodMk hy).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hq] with p hp
  exact finiteLocal_value L p hp

/-- The original native infinity coordinates define a genuine local map
into the INDEPENDENT polynomial zero locus. Fallback is used only outside
the proved original neighborhood and cannot enter its germ. -/
@[expose] def infinityLocal (q : Torus L) : InfinityPlane L :=
  if hq:infinityEquation L (nativeU L q,nativeV L q)=0 then
    ⟨(nativeU L q,nativeV L q),hq⟩ else origin L
lemma infinityLocal_value (q : Torus L)
    (hq:infinityEquation L (nativeU L q,nativeV L q)=0) :
    (infinityLocal L q).val=(nativeU L q,nativeV L q) := by
  rw [infinityLocal,dif_pos hq]
lemma infinityLocal_zero : infinityLocal L 0=origin L := by
  apply Subtype.ext
  have hq : infinityEquation L (nativeU L 0,nativeV L 0)=0 := by
    simp [nativeU_zero,nativeV_zero,infinityEquation]
  rw [infinityLocal_value L 0 hq,nativeU_zero,nativeV_zero]
  rfl
lemma infinityLocal_continuous : ContinuousAt (infinityLocal L) (0:Torus L) := by
  apply tendsto_subtype_rng.mpr
  have hh := OriginalPeriodNativeChartGerms318.holomorphic L
  apply (hh.1.continuousAt.prodMk hh.2.continuousAt).congr_of_eventuallyEq
  filter_upwards [infinity_equation L] with q hq
  exact infinityLocal_value L q hq

/-- On a WHOLE original pole neighborhood, including zero, the original
point map is precisely the actual infinity chart inclusion applied to the
constructed native holomorphic coordinates. -/
theorem whole_pole_identity : ∀ᶠ q in 𝓝 (0:Torus L),
    originalPoint L q=infinityChart L (infinityLocal L q) := by
  filter_upwards [infinity_equation L,OriginalPeriodNativeChartGerms318.overlap L] with q he ho
  by_cases hq:q=0
  · subst q
    rw [original_zero,infinityLocal_zero]
  · obtain ⟨hy,hu,hv⟩ := ho hq
    rw [original_nonzero L q hq]
    apply (chart_identification L _ _).mpr
    have hp := original_coordinates L ⟨q,hq⟩
    have hny : (originalFinite L ⟨q,hq⟩).val.2≠0 := by simpa only [hp] using hy
    refine ⟨hny,?_⟩
    apply Subtype.ext
    rw [toInfinity_value L _ hny,infinityLocal_value L q he,hp]
    exact Prod.ext hu.symm hv.symm

/-- Continuity is proved against the independent completed topology,
not installed by the pre-existing set bijection. The pole uses its full
native infinity neighborhood rather than punctured limiting values. -/
theorem original_continuous : Continuous (originalPoint L) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hq:q=0
  · subst q
    apply ((infinity_open L).continuous.continuousAt.comp _ (infinityLocal_continuous L)).congr_of_eventuallyEq
    exact whole_pole_identity L
  · apply ((finite_open L).continuous.continuousAt.comp q (finiteLocal_continuous L q hq)).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hq] with p hp
    rw [original_nonzero L p hp,finiteLocal,dif_pos hp]

/-- The independently glued polynomial target is compact because the
actual continuous original map covers it. Hausdorffness and inverse
analyticity are separate, not inferred from continuous bijectivity. -/
theorem completed_compact : CompactSpace (CompletedPlane L) :=
  ⟨by
    simpa only [Set.image_univ,(original_bijective L).2.range_eq] using
      (isCompact_univ.image (original_continuous L))⟩
end OriginalPeriodIndependentContinuity318
