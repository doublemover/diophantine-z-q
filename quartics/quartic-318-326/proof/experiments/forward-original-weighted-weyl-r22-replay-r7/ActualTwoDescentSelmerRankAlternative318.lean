module
public import ActualTwoDescentSelmerObstructionComparison318
public section
noncomputable section
namespace ActualTwoDescentSelmerRankAlternative318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentCohomologicalSelmer318 ActualTwoDescentActualSelmerCardinality318
open ActualTwoDescentSelmerObstructionComparison318 ActualTwoDescentObstructionCardinality318

/-- Even the genuine2-Selmer count8 leaves EXACTLY the unresolved rank-zero/order-two versus rank-one/trivial alternative. -/
theorem actual_selmer_rank_alternative (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (cohomologicalSelmer n hn)=8) :
    (Nat.card (DoubleQuotient n)=4 ∧ Nat.card (SelmerObstruction n hn)=2 ∧ Finite (Point n)) ∨
    (Nat.card (DoubleQuotient n)=8 ∧ Nat.card (SelmerObstruction n hn)=1 ∧ Infinite (Point n)) := by
  have hlocal : Nat.card (ActualTwoDescentAllPlacesIntersection318.allPlacesImage n hn)=8 :=
    (actual_selmer_cardinality n hn).symm.trans hS
  simpa only [actual_selmer_obstruction_card] using actual_obstruction_alternative n hn hf hb hlocal

end ActualTwoDescentSelmerRankAlternative318
