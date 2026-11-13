module
public import ActualDenominatorOrientationChoice318
public section
noncomputable section
namespace ActualDenominatorCandidateReduction318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 ActualQuarterDenominatorCoverage318
open ActualOrderOrientationCandidates318 ActualDenominatorOrientationChoice318
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
theorem reduction (r : Roots C u w hv)
    (hlarge : ∀ i : Fin 3 × Fin 5,49<(row C u w i.1 i.2).natAbs)
    (hroots : SelectedQuarterOrder318.RootData C u w hv) (L h0 q : ℕ) (hq : q.Prime)
    (ht : ∀ i,Test C u w hv r false i q ∨ Test C u w hv r true i q) :
    (candidates C u w hv r L h0).card≤2 ∧
    ((candidates C u w hv r L h0).Nonempty ↔
      choice C u w hv r q∈candidates C u w hv r L h0 ∨
      FiniteOrderSignChoices318.flip (choice C u w hv r q)∈candidates C u w hv r L h0) := by
  have hd:=actual_divisors C u w hv r hlarge hroots q hq ht
  exact ⟨ActualCommonPrimeCandidates318.card_le_two C u w hv r L h0 q hq _ hd,
    ActualCommonPrimeCandidates318.nonempty_iff C u w hv r L h0 q hq _ hd⟩
end ActualDenominatorCandidateReduction318
