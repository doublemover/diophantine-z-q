module
public import ActualOriginalFiveAxisCancellation318
public section
noncomputable section
namespace ActualOriginalPositiveOverlapRectangle318
open QuadricCRTAssembly318 ActualOriginalCanonicalSupportBox318
open ActualOriginalCanonicalOverlapLength318 ActualOriginalFiniteBoxProduct318
open ActualOriginalBoxOverlap318 ActualOriginalCorrelationBasePoints318
open ActualOriginalWeightedWeylIdentity318 ActualOriginalCompactCircleCount318
open ActualOriginalScaledPairedMixedDifference318 ActualOriginalFiveAxisCancellation318
open ActualOriginalLinearRectangle318
open scoped BigOperators

@[expose] def overlapStart (H u : ℤ) : ℤ := max (-H) (-H-u)
@[expose] def overlapSteps (H u : ℤ) : ℕ := (min H (H-u)-overlapStart H u).toNat
@[expose] def overlapCorner (H : ℤ) (h : Coordinates ℤ) : Coordinates ℤ :=
  ((overlapStart H h.1.1,overlapStart H h.1.2),
    (overlapStart H h.2.1.1,overlapStart H h.2.1.2),overlapStart H h.2.2)

lemma actual_overlap_positive_length (H u : ℤ) (hH : 0≤H)
    (hu : u∈Finset.Icc (-(2*H)) (2*H)) :
    overlapLength H u=overlapSteps H u+1 := by
  obtain ⟨hul,huh⟩ := Finset.mem_Icc.mp hu
  have horder : max (-H) (-H-u)≤min H (H-u) := by
    apply max_le
    · apply le_min <;> omega
    · apply le_min <;> omega
  unfold overlapLength overlapSteps overlapStart
  omega

lemma actual_overlap_steps_le (H u : ℤ) (hH : 0≤H)
    (hu : u∈Finset.Icc (-(2*H)) (2*H)) :
    (overlapSteps H u : ℝ)+1≤2*(H : ℝ)+1 := by
  have hh : (overlapLength H u : ℝ)≤2*(H : ℝ)+1 := by
    exact_mod_cast actual_overlap_length_le H u hH
  simpa only [actual_overlap_positive_length H u hH hu,Nat.cast_add,Nat.cast_one] using hh

/-- Every displacement admitted from the actual doubled box has five
NONEMPTY actual overlap intervals. No empty fiber is silently assigned a
positive rectangle. All actual difference fibers satisfy this hypothesis. -/
theorem actual_correlation_five_rectangle (κ H : ℤ) (B : ℝ) (W : Coordinates ℝ → ℝ)
    (θ : AddCircle (1 : ℝ)) (h : Coordinates ℤ) (hH : 0≤H)
    (hh : h∈centeredBox (2*H)) :
    linearCorrelation κ (centeredBox H) (latticeWeight B W) θ h=
      originalLinearRectangle κ (latticePairedWeight B W h) θ h
        (fiveAxes (overlapSteps H h.1.1) (overlapSteps H h.1.2)
          (overlapSteps H h.2.1.1) (overlapSteps H h.2.1.2) (overlapSteps H h.2.2))
        (overlapCorner H h) := by
  have hb := hh
  simp only [centeredBox,originalBox,Finset.mem_product] at hb
  have h₀ := actual_overlap_positive_length H h.1.1 hH hb.1.1
  have h₁ := actual_overlap_positive_length H h.1.2 hH hb.1.2
  have h₂ := actual_overlap_positive_length H h.2.1.1 hH hb.2.1.1
  have h₃ := actual_overlap_positive_length H h.2.1.2 hH hb.2.1.2
  have h₄ := actual_overlap_positive_length H h.2.2 hH hb.2.2
  rw [actual_correlation_base_points,actual_box_base_points,actual_original_five_rectangle_identity]
  simp only [originalBox,Finset.sum_product]
  simp_rw [actual_canonical_overlap_sum]
  rw [h₀,h₁,h₂,h₃,h₄]
  rfl

end ActualOriginalPositiveOverlapRectangle318
