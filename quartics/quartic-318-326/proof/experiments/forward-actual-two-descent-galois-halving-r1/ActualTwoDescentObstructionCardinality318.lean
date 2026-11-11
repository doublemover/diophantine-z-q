module
public import ActualTwoDescentRationalQuotientAlternative318
public section
noncomputable section
namespace ActualTwoDescentObstructionCardinality318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentConcreteLocalObstruction318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentRationalImageCardinality318 ActualTwoDescentRationalQuotientAlternative318

/-- Exact alternative: rational quotient4 and obstruction2, or rational quotient8 and obstruction1. -/
theorem actual_obstruction_alternative (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hbound : Nat.card (DoubleQuotient n) ≤ 8)
    (hlocal : Nat.card (allPlacesImage n hn)=8) :
    (Nat.card (DoubleQuotient n)=4 ∧ Nat.card (LocalObstruction n hn)=2 ∧ Finite (Point n)) ∨
    (Nat.card (DoubleQuotient n)=8 ∧ Nat.card (LocalObstruction n hn)=1 ∧ Infinite (Point n)) := by
  have hprod := actual_rational_obstruction_product n hn
  rw [hlocal] at hprod
  rcases actual_quotient_four_or_eight n hn hf hbound with h4|h8
  · left
    refine ⟨h4,?_,actual_finite_of_quotient_four n hn hf hbound h4⟩
    rw [h4] at hprod
    omega
  · right
    refine ⟨h8,?_,actual_infinite_of_quotient_eight n hn h8⟩
    rw [h8] at hprod
    omega

lemma actual_obstruction_one_iff_infinite (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hbound : Nat.card (DoubleQuotient n) ≤ 8)
    (hlocal : Nat.card (allPlacesImage n hn)=8) :
    Nat.card (LocalObstruction n hn)=1 ↔ Infinite (Point n) := by
  have hprod := actual_rational_obstruction_product n hn
  rw [hlocal] at hprod
  constructor
  · intro h
    have he : Nat.card (DoubleQuotient n)=8 := by simpa only [h,mul_one] using hprod
    exact actual_infinite_of_quotient_eight n hn he
  · intro h
    have he := (actual_infinite_iff_quotient_eight n hn hf hbound).mp h
    rw [he] at hprod
    omega

lemma actual_obstruction_card_le_two (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hbound : Nat.card (DoubleQuotient n) ≤ 8)
    (hlocal : Nat.card (allPlacesImage n hn)=8) : Nat.card (LocalObstruction n hn) ≤ 2 := by
  rcases actual_obstruction_alternative n hn hf hbound hlocal with ⟨_,h,_⟩|⟨_,h,_⟩ <;> omega

end ActualTwoDescentObstructionCardinality318
