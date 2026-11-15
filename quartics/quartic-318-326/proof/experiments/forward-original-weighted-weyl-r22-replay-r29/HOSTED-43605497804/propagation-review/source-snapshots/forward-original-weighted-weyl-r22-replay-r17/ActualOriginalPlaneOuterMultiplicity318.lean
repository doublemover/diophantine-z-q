module
public import ActualOriginalSmoothOverlapPlane318
public section
noncomputable section
namespace ActualOriginalPlaneOuterMultiplicity318
open QuadricCRTAssembly318 ActualOriginalBoxPlaneAggregation318
open ActualOriginalWeightedWeylIdentity318 ActualOriginalBoxOverlap318
open ActualOriginalCanonicalSupportBox318
open scoped BigOperators

lemma actual_overlap_card_le (H h : ℤ) (hH : 0≤H) :
    ((overlap (Finset.Icc (-H) H) h).card : ℝ)≤2*(H : ℝ)+1 := by
  have hc := Finset.card_filter_le (Finset.Icc (-H) H) (fun y => h+y∈Finset.Icc (-H) H)
  rw [Int.card_Icc] at hc
  have hi : ((overlap (Finset.Icc (-H) H) h).card : ℤ)≤2*H+1 := by
    unfold overlap
    omega
  exact_mod_cast hi

/-- The THREE outer overlap multiplicities are explicitly charged.
This bound never identifies a five-dimensional displacement with one or
two frequencies. -/
theorem actual_canonical_plane_outer_budget (κ H : ℤ) (w : Coordinates ℤ → ℂ)
    (θ : AddCircle (1 : ℝ)) (hH : 0≤H) (K : Coordinates ℤ → ℝ)
    (hK : ∀ h, 0≤K h)
    (hb : ∀ h c d e, ‖overlapPlaneCorrelation κ H w θ h c d e‖≤K h) :
    canonicalPlaneBudget κ H w θ≤
      (2*(H : ℝ)+1)^3*(∑ h∈differences (centeredBox H), K h) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  have hn : (0 : ℝ)≤2*(H : ℝ)+1 := by exact_mod_cast (show (0 : ℤ)≤2*H+1 by omega)
  calc
    _ ≤ ∑ c∈overlap (Finset.Icc (-H) H) h.2.1.1,
        ∑ d∈overlap (Finset.Icc (-H) H) h.2.1.2,
        ∑ e∈overlap (Finset.Icc (-H) H) h.2.2, K h := by
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.sum_le_sum (fun e he => hb h c d e)
    _ = ((overlap (Finset.Icc (-H) H) h.2.1.1).card : ℝ)*
        (((overlap (Finset.Icc (-H) H) h.2.1.2).card : ℝ)*
        (((overlap (Finset.Icc (-H) H) h.2.2).card : ℝ)*K h)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (2*(H : ℝ)+1)*((2*(H : ℝ)+1)*((2*(H : ℝ)+1)*K h)) := by
      apply mul_le_mul (actual_overlap_card_le H h.2.1.1 hH)
      · apply mul_le_mul (actual_overlap_card_le H h.2.1.2 hH)
        · exact mul_le_mul_of_nonneg_right (actual_overlap_card_le H h.2.2 hH) (hK h)
        · exact mul_nonneg (by positivity) (hK h)
        · exact hn
      · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hK h))
      · exact hn
    _ = _ := by ring

end ActualOriginalPlaneOuterMultiplicity318
