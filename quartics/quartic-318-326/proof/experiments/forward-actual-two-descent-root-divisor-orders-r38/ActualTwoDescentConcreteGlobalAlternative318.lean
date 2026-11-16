module
public import ActualTwoDescentBetaPointRankEquivalence318
public section
noncomputable section
namespace ActualTwoDescentConcreteGlobalAlternative318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentConcreteLocalObstruction318 ActualTwoDescentObstructionCardinality318
open ActualTwoDescentActualQuotientControl318 ActualTwoDescentOriginalAllPlacesCardinality318

/-- An exact actual-group alternative, not a named placeholder for a rank theorem. -/
def GlobalAlternative (n : ℚ) (hn : n ≠ 0) : Prop :=
  (Finite (Point n) ∧ Nat.card (DoubleQuotient n)=4 ∧ Nat.card (LocalObstruction n hn)=2) ∨
  (Infinite (Point n) ∧ Nat.card (DoubleQuotient n)=8 ∧ Nat.card (LocalObstruction n hn)=1)

lemma actual_global_alternative (n b : ℕ) (hn : n ≠ 0)
    (C : QuotientControl n b) (H : AllPlacesEight n) : GlobalAlternative (n : ℚ) (Nat.cast_ne_zero.mpr hn) := by
  obtain ⟨_,hlocal⟩ := H
  rcases actual_obstruction_alternative (n : ℚ) (Nat.cast_ne_zero.mpr hn) C.2.1 C.2.2.1 hlocal with
    ⟨hq,ho,hf⟩|⟨hq,ho,hi⟩
  · exact Or.inl ⟨hf,hq,ho⟩
  · exact Or.inr ⟨hi,hq,ho⟩

end ActualTwoDescentConcreteGlobalAlternative318
