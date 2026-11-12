module
public import ConcreteGaussianOppositePrimeFactor318
public section
noncomputable section
namespace ActualFiniteDenominatorCoverage318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 ActualFiniteRootFamily318 SelectedReductionOrder318
open SelectedEntryDenominatorDivisibility318
variable {labels : Fin 4→ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- Exact FINITE count/denominator data, with no actual-order divisibility
in its fields. Successful tests remain arithmetic conditions to verify. -/
@[expose] def Test (d : Data C u w) (b : Bool) (i : Fin 3×Fin 5) (q : ℕ) : Prop :=
  let N := finiteCounts C u w hv d b i/4
  0<N ∧ q∣N ∧ ¬(row C u w i.1 i.2).natAbs∣multipleDenominator (N/q)
lemma factor (hlarge : ∀ i : Fin 3×Fin 5,49<(row C u w i.1 i.2).natAbs)
    (d : Data C u w) (b : Bool) (i : Fin 3×Fin 5) (q : ℕ) (hq : q.Prime)
    (htest : Test C u w hv d b i q) :
    q∣if b then oppositeOrder C u w hv (roots C u w hv hlarge d) i
      else primaryOrder C u w hv (roots C u w hv hlarge d) i := by
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
  have hp : p≠2 := by have hl:=hlarge i;omega
  have h7 : ¬p∣49 := by
    intro hd
    have hh:=Nat.le_of_dvd (by decide : 0<49) hd
    have hl:=hlarge i
    omega
  obtain ⟨hN,hqd,hden⟩:=htest
  have he:=counts_match C u w hv hlarge d b i
  cases b
  · change pointCount p ((roots C u w hv hlarge d) i).val
      ((roots C u w hv hlarge d) i).property=finiteCounts C u w hv d false i at he
    rw [←he] at hN hqd hden
    exact SelectedCountDenominatorFactors318.quarter_count p _ _ hp h7
      (d i).eighth (d i).fourth (d i).eighth_pow (d i).fourth_pow q hq hN hqd hden
  · change pointCount p (-((roots C u w hv hlarge d) i).val)
      (ConcretePadic318.negative_root p _ _)=finiteCounts C u w hv d true i at he
    rw [←he] at hN hqd hden
    exact SelectedCountDenominatorFactors318.quarter_count p _ _ hp h7
      (d i).eighth (d i).fourth (d i).eighth_pow (d i).fourth_pow q hq hN hqd hden
/-- This PRODUCES actual common-divisor coverage from the finite tests.
It does not assert that all tests can succeed at one simultaneous tuple. -/
theorem coverage (hlarge : ∀ i : Fin 3×Fin 5,49<(row C u w i.1 i.2).natAbs)
    (d : Data C u w) (q : ℕ) (hq : q.Prime)
    (htest : ∀ i,Test C u w hv d false i q ∨ Test C u w hv d true i q) :
    ∀ i,q∣primaryOrder C u w hv (roots C u w hv hlarge d) i ∨
      q∣oppositeOrder C u w hv (roots C u w hv hlarge d) i := by
  intro i
  rcases htest i with hm|hp
  · exact Or.inl (factor C u w hv hlarge d false i q hq hm)
  · exact Or.inr (factor C u w hv hlarge d true i q hq hp)
end ActualFiniteDenominatorCoverage318
