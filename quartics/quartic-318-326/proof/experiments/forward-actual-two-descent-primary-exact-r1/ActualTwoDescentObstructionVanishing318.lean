module
public import ActualTwoDescentObstructionCardinality318
public section
noncomputable section
namespace ActualTwoDescentObstructionVanishing318
set_option maxHeartbeats 16000000

open ActualTwoDescentConcreteLocalObstruction318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentEllipticModel318
open ActualTwoDescentObstructionCardinality318

/-- Triviality of the ACTUAL quotient is equivalent to vanishing of all its literal classes. -/
lemma actual_obstruction_one_iff_vanishes (n : ℚ) (hn : n ≠ 0) :
    Nat.card (LocalObstruction n hn)=1 ↔
      ∀ z : allPlacesImage n hn, (QuotientGroup.mk z : LocalObstruction n hn)=1 := by
  constructor
  · intro h
    letI : Subsingleton (LocalObstruction n hn) := (Nat.card_eq_one_iff_unique.mp h).1
    intro z
    exact Subsingleton.elim _ _
  · intro h
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨⟨?_⟩,inferInstance⟩
    intro x y
    have hone : ∀ q : LocalObstruction n hn, q=1 := by
      intro q
      refine QuotientGroup.induction_on q ?_
      exact h
    exact (hone x).trans (hone y).symm

/-- The remaining global theorem is literally equivalent to rational-image equality. -/
theorem actual_infinite_iff_local_global (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hbound : Nat.card (DoubleQuotient n) ≤ 8)
    (hlocal : Nat.card (allPlacesImage n hn)=8) :
    Infinite (Point n) ↔ allPlacesImage n hn=ActualTwoDescentLocalImageSubgroup318.actualKummerImage n hn := by
  rw [←actual_obstruction_one_iff_infinite n hn hf hbound hlocal,
    actual_obstruction_one_iff_vanishes,actual_all_obstructions_vanish_iff]

end ActualTwoDescentObstructionVanishing318
