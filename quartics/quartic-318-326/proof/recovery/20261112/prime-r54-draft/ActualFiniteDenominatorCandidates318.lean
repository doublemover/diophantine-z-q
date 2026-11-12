module
public import ActualFiniteDenominatorCoverage318
public section
noncomputable section
namespace ActualFiniteDenominatorCandidates318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 ActualFiniteRootFamily318 ActualFiniteDenominatorCoverage318
variable {labels : Fin 4→ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- Native finite-field lifts and explicit denominator tests now feed the
EXISTING two-choice orientation consumer. No supplied actual-order
coverage remains, but SAME-tuple prime values and successful tests do. -/
theorem candidates_card (hlarge : ∀ i : Fin 3×Fin 5,49<(row C u w i.1 i.2).natAbs)
    (d : Data C u w) (q : ℕ) (hq : q.Prime)
    (htest : ∀ i,Test C u w hv d false i q ∨ Test C u w hv d true i q)
    (L h₀ : ℕ) :
    (ActualFiniteRootOrientations318.candidates C u w hv (roots C u w hv hlarge d) L h₀).card≤2 :=
  ActualCommonPrimeCandidates318.card_le_two C u w hv _ q hq
    (coverage C u w hv hlarge d q hq htest) L h₀
/-- Exact success criterion after the produced coverage, still not an
existence theorem for either candidate. -/
theorem candidates_nonempty (hlarge : ∀ i : Fin 3×Fin 5,49<(row C u w i.1 i.2).natAbs)
    (d : Data C u w) (q : ℕ) (hq : q.Prime)
    (htest : ∀ i,Test C u w hv d false i q ∨ Test C u w hv d true i q)
    (L h₀ : ℕ) :
    (ActualFiniteRootOrientations318.candidates C u w hv (roots C u w hv hlarge d) L h₀).Nonempty ↔
      ActualCommonPrimeCandidates318.choice C u w hv (roots C u w hv hlarge d) q∈
        ActualFiniteRootOrientations318.candidates C u w hv (roots C u w hv hlarge d) L h₀ ∨
      FiniteOrderCommonPrimeOrientation318.flip
        (ActualCommonPrimeCandidates318.choice C u w hv (roots C u w hv hlarge d) q)∈
        ActualFiniteRootOrientations318.candidates C u w hv (roots C u w hv hlarge d) L h₀ :=
  ActualCommonPrimeCandidates318.nonempty_iff C u w hv _ q hq
    (coverage C u w hv hlarge d q hq htest) L h₀
end ActualFiniteDenominatorCandidates318
