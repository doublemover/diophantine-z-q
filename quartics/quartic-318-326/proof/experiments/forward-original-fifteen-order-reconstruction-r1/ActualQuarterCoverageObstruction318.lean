module
public import ActualOrderContinuityCRT318
public section
noncomputable section
namespace ActualQuarterCoverageObstruction318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 ActualQuarterDenominatorCoverage318
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- Simultaneous successful tests at opposite sides of ANY two positions obstruct
coprimality of the literal two LCMs. Positions may coincide or share a prime. -/
theorem cross_obstruction (r : Roots C u w hv)
    (hlarge : ∀ i : Fin 3 × Fin 5,49<(row C u w i.1 i.2).natAbs)
    (hroots : SelectedQuarterOrder318.RootData C u w hv)
    (q : ℕ) (hq : q.Prime) (i j : Fin 3 × Fin 5)
    (hm : Test C u w hv r false i q) (hp : Test C u w hv r true j q) :
    ¬Nat.Coprime (minus C u w hv r) (plus C u w hv r) := by
  intro hcop
  have ha : q∣minus C u w hv r :=
    (factor C u w hv r hlarge hroots false i q hq hm).trans (primary_dvd C u w hv r i)
  have hb : q∣plus C u w hv r :=
    (factor C u w hv r hlarge hroots true j q hq hp).trans (opposite_dvd C u w hv r j)
  have hg := Nat.dvd_gcd ha hb
  rw [hcop.gcd_eq_one] at hg
  exact hq.not_dvd_one hg
end ActualQuarterCoverageObstruction318
