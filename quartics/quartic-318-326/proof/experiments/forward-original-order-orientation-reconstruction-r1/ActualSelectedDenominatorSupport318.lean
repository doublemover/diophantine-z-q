module
public import ActualOrderAnnihilatorLCM318
public section
noncomputable section
namespace ActualSelectedDenominatorSupport318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 SelectedEntryDenominatorDivisibility318
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- A positive common annihilator forces EVERY selected prime into one fixed denominator. -/
lemma primary_divisors (r : Roots C u w hv) (M : ℕ) (hM : 0<M)
    (h : minus C u w hv r∣M) :
    ∀ i : Fin 3 × Fin 5, (row C u w i.1 i.2).natAbs∣multipleDenominator M := by
  intro i
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
  exact order_divides p (r i).val (r i).property M hM
    ((primary_dvd C u w hv r i).trans h)
lemma opposite_divisors (r : Roots C u w hv) (M : ℕ) (hM : 0<M)
    (h : plus C u w hv r∣M) :
    ∀ i : Fin 3 × Fin 5, (row C u w i.1 i.2).natAbs∣multipleDenominator M := by
  intro i
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
  exact order_divides p (-(r i).val) (ConcretePadic318.negative_root p _ _) M hM
    ((opposite_dvd C u w hv r i).trans h)
/-- Even one sufficiently large selected prime rules out either fixed positive annihilator.
This does NOT rule out a fixed prime dividing all the actual orders. -/
theorem fixed_annihilator_obstruction (r : Roots C u w hv) (M : ℕ) (hM : 0<M)
    (i : Fin 3 × Fin 5) (hp : multipleDenominator M<(row C u w i.1 i.2).natAbs) :
    ¬minus C u w hv r∣M ∧ ¬plus C u w hv r∣M := by
  constructor
  · intro h
    exact (not_le_of_gt hp) (Nat.le_of_dvd (positive M) (primary_divisors C u w hv r M hM h i))
  · intro h
    exact (not_le_of_gt hp) (Nat.le_of_dvd (positive M) (opposite_divisors C u w hv r M hM h i))
end ActualSelectedDenominatorSupport318
