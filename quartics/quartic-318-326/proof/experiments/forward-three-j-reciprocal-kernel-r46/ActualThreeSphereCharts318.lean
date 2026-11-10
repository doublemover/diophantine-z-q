module
public import ActualThreeEndOrders318
public import Mathlib.Topology.Compactification.OnePoint.Basic
public section
noncomputable section
open Filter Topology WithTop.LinearOrderedAddCommGroup
open scoped OnePoint
namespace ActualThreeSphereCharts318
open ActualThreeQParameter318 ActualThreeEndOrders318 ActualThreeCuspExhaustion318
open FiniteCuspEnds318 ActualThreeCuspOverlap318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] def boundaryValue (c : End 3) : OnePoint ℂ :=
  if c = infinityEnd then ∞ else (0:ℂ)

lemma boundary_infinity : boundaryValue infinityEnd = ∞ := by simp [boundaryValue]
lemma boundary_zero : boundaryValue zeroEnd = (0:ℂ) := by
  simp [boundaryValue,ends_distinct.symm]

/-- The original source q-to-T map, completed at its actual selected cusp origin. -/
@[expose] def sphereChart (c : End 3) (q : ℂ) : OnePoint ℂ :=
  if q=0 then boundaryValue c else (qParameter (representative 3 c) q : OnePoint ℂ)

lemma sphereChart_zero (c : End 3) : sphereChart c 0 = boundaryValue c := by simp [sphereChart]
lemma sphereChart_nonzero (c : End 3) {q : ℂ} (hq : q ≠ 0) :
    sphereChart c q = (qParameter (representative 3 c) q : OnePoint ℂ) := by simp [sphereChart,hq]

/-- The actual meromorphic orders give continuity into the independent standard
one-point compactification of C at both selected source-cusp origins. -/
theorem sphereChart_continuousAt_zero (c : End 3) : ContinuousAt (sphereChart c) 0 := by
  rw [continuousAt_iff_punctured_nhds,sphereChart_zero]
  have he : sphereChart c =ᶠ[𝓝[≠] (0:ℂ)]
      (fun q => (qParameter (representative 3 c) q : OnePoint ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact sphereChart_nonzero c hq
  apply Filter.Tendsto.congr' he.symm
  rcases end_exhaustion c with rfl | rfl
  · rw [boundary_infinity]
    have hp := tendsto_cobounded_of_meromorphicOrderAt_neg
      (show meromorphicOrderAt (qParameter (representative 3 infinityEnd)) 0 < 0 by
        rw [representative_infinity_order]
        exact WithTop.coe_lt_coe.mpr (show (-1:ℤ) < 0 by decide))
    have ht : Tendsto ((↑) : ℂ → OnePoint ℂ) (Bornology.cobounded ℂ) (𝓝 ∞) := by
      simpa only [coclosedCompact_eq_cocompact,Metric.cobounded_eq_cocompact] using
        (OnePoint.tendsto_coe_infty (X:=ℂ))
    exact ht.comp hp
  · rw [boundary_zero]
    have hz := tendsto_zero_of_meromorphicOrderAt_pos
      (show 0 < meromorphicOrderAt (qParameter (representative 3 zeroEnd)) 0 by
        rw [representative_zero_order]; norm_num)
    exact OnePoint.continuous_coe.continuousAt.tendsto.comp hz

/-- Continuity holds on the full genuine selected width-disc, not just its germ. -/
theorem sphereChart_continuousOn (c : End 3) : ContinuousOn (sphereChart c) (disc c) := by
  intro q hq
  apply ContinuousAt.continuousWithinAt
  by_cases hz : q=0
  · subst q
    exact sphereChart_continuousAt_zero c
  · have ha := qParameter_analytic (representative 3 c) q ⟨hz,hq⟩
    apply (OnePoint.continuous_coe.continuousAt.comp ha.continuousAt).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with r hr
    exact sphereChart_nonzero c hr

end ActualThreeSphereCharts318
