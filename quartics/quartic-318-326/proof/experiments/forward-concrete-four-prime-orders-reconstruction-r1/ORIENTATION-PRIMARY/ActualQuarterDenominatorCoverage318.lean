module
public import ActualSelectedDenominatorSupport318
public section
noncomputable section
namespace ActualQuarterDenominatorCoverage318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 SelectedReductionOrder318 SelectedEntryDenominatorDivisibility318
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- Literal finite-curve count at the residue of the SAME original chosen root. -/
@[expose] def Test (r : Roots C u w hv) (b : Bool) (i : Fin 3 × Fin 5) (q : ℕ) : Prop :=
  let N := counts C u w hv r b i/4
  0<N ∧ q∣N ∧ ¬(row C u w i.1 i.2).natAbs∣multipleDenominator (N/q)
lemma factor (r : Roots C u w hv)
    (hlarge : ∀ i : Fin 3 × Fin 5,49<(row C u w i.1 i.2).natAbs)
    (hroots : SelectedQuarterOrder318.RootData C u w hv)
    (b : Bool) (i : Fin 3 × Fin 5) (q : ℕ) (hq : q.Prime)
    (ht : Test C u w hv r b i q) :
    q∣if b then oppositeOrder C u w hv r i else primaryOrder C u w hv r i := by
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
  have hp : p≠2 := by have h:=hlarge i;omega
  have h7 : ¬p∣49 := by
    intro h
    have he:=Nat.le_of_dvd (by decide : 0<49) h
    have hl:=hlarge i
    omega
  obtain ⟨z,t,hz,ht'⟩:=hroots i
  obtain ⟨hN,hqd,hden⟩:=ht
  cases b
  · exact SelectedCountDenominatorFactors318.quarter_count p (r i).val (r i).property
      hp h7 z t hz ht' q hq hN hqd hden
  · exact SelectedCountDenominatorFactors318.quarter_count p (-(r i).val)
      (ConcretePadic318.negative_root p _ _) hp h7 z t hz ht' q hq hN hqd hden
/-- Genuine actual common-prime coverage follows IF these explicit finite denominator tests
succeed at all positions of the SAME simultaneous-prime tuple. Success is not asserted. -/
theorem coverage (r : Roots C u w hv)
    (hlarge : ∀ i : Fin 3 × Fin 5,49<(row C u w i.1 i.2).natAbs)
    (hroots : SelectedQuarterOrder318.RootData C u w hv)
    (q : ℕ) (hq : q.Prime)
    (htest : ∀ i,Test C u w hv r false i q ∨ Test C u w hv r true i q) :
    ∀ i,q∣primaryOrder C u w hv r i ∨ q∣oppositeOrder C u w hv r i := by
  intro i
  rcases htest i with h|h
  · exact Or.inl (factor C u w hv r hlarge hroots false i q hq h)
  · exact Or.inr (factor C u w hv r hlarge hroots true i q hq h)
end ActualQuarterDenominatorCoverage318
