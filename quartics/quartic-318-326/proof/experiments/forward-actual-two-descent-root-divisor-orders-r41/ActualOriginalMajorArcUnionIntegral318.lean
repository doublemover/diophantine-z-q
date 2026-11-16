module
public import ActualOriginalMajorArcDomain318
public import ActualOriginalGrowingMajorArcLimit318
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public section
noncomputable section
namespace ActualOriginalMajorArcUnionIntegral318
open QuadricCRTAssembly318 ActualOriginalMajorArcDomain318 ActualOriginalMajorArcIntegral318
open ActualOriginalCompactCircleCount318 ActualOriginalScaledCircle318
open MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- The indexed actual major-arc integral equals the integral over its
literal measurable set union. A shifted fundamental interval retains the
whole modulus-one arc; no boundary arc is silently removed. -/
theorem actual_major_union_integral (κ : ℤ) (N : ℕ) (B : ℝ) (hB : 0 < B)
    (hscale : ((N : ℝ)+1)^3 ≤ B) (W : Coordinates ℝ → ℝ) (hW : HasCompactSupport W) :
    (∫ θ in majorDomain N B, scaledCircleSum κ θ B W) =
      majorArcIntegral κ N B (N : ℝ) W := by
  classical
  have hc := actual_scaled_circle_continuous κ B hB.ne' W hW
  have hi (i : ArcIndex N) : IntegrableOn (fun θ => scaledCircleSum κ θ B W) (arc B i) := by
    exact (hc.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [majorDomain,integral_iUnion_fintype (fun _ => measurableSet_Ioc)
    (arcs_pairwise N B hB hscale) hi]
  rw [Fintype.sum_sigma]
  unfold majorArcIntegral
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro a ha
  have hr : 0 ≤ radius N B := by unfold radius; positivity
  rw [intervalIntegral.integral_comp_add_left]
  rw [intervalIntegral.integral_of_le (by dsimp [radius] at hr; linarith)]
  simp only [arc,center,radius,sub_eq_add_neg,neg_div]

end ActualOriginalMajorArcUnionIntegral318
