module
public import ActualTwoDescentSelmerSquareclassComparison318
public section
noncomputable section
namespace ActualTwoDescentActualSelmerCardinality318
set_option maxHeartbeats 16000000

open ActualTwoDescentCohomologicalSelmer318 ActualTwoDescentSelmerSquareclassComparison318
open ActualTwoDescentAllPlacesIntersection318 ActualTwoDescentOriginalAllPlacesCardinality318

lemma actual_selmer_cardinality (n : ℚ) (hn : n ≠ 0) :
    Nat.card (cohomologicalSelmer n hn)=Nat.card (allPlacesImage n hn) :=
  Nat.card_congr (selmerSquareclassEquiv n hn).toEquiv

/-- The previously constructed actual all-place count now proves the cardinality of the GENUINE cohomological2-Selmer group. -/
theorem actual_selmer_eight (n : ℕ) (H : AllPlacesEight n) :
    ∃ hn : n ≠ 0, Nat.card (cohomologicalSelmer (n : ℚ) (Nat.cast_ne_zero.mpr hn))=8 := by
  obtain ⟨hn,hcard⟩ := H
  exact ⟨hn,(actual_selmer_cardinality (n : ℚ) (Nat.cast_ne_zero.mpr hn)).trans hcard⟩

end ActualTwoDescentActualSelmerCardinality318
