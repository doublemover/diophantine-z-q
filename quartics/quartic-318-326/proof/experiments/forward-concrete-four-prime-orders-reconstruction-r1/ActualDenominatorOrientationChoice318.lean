module
public import ActualCommonPrimeCandidates318
public section
noncomputable section
namespace ActualDenominatorOrientationChoice318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 ActualQuarterDenominatorCoverage318
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- Choose from successful literal quarter-count/denominator tests, not from assumed order values. -/
@[expose] def choice (r : Roots C u w hv) (q : ℕ) : Fin 3 × Fin 5 → Bool := by
  classical
  exact fun i => if Test C u w hv r false i q then false else true
lemma chosen_tests (r : Roots C u w hv) (q : ℕ)
    (ht : ∀ i,Test C u w hv r false i q ∨ Test C u w hv r true i q) :
    ∀ i,Test C u w hv r (choice C u w hv r q i) i q := by
  classical
  intro i
  by_cases h : Test C u w hv r false i q
  · simpa only [choice,h,if_pos] using h
  · simpa only [choice,h,if_neg] using (ht i).resolve_left h
/-- Actual common-divisor coverage in the chosen orientation is PRODUCED. -/
theorem actual_divisors (r : Roots C u w hv)
    (hlarge : ∀ i : Fin 3 × Fin 5,49<(row C u w i.1 i.2).natAbs)
    (hroots : SelectedQuarterOrder318.RootData C u w hv) (q : ℕ) (hq : q.Prime)
    (ht : ∀ i,Test C u w hv r false i q ∨ Test C u w hv r true i q) :
    ∀ i,q∣FiniteOrderSignChoices318.left (primaryOrder C u w hv r)
      (oppositeOrder C u w hv r) (choice C u w hv r q) i := by
  intro i
  exact factor C u w hv r hlarge hroots (choice C u w hv r q i) i q hq
    (chosen_tests C u w hv r q ht i)
end ActualDenominatorOrientationChoice318
