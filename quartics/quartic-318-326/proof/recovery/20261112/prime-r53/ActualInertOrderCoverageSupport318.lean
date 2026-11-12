module
public import ActualQuadraticCoefficientContent318
public section
noncomputable section
namespace ActualInertOrderCoverageSupport318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318
variable {labels : Fin 4→ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- Exact necessary support for a COMMON prime DIVIDING one actual order
at EVERY original position, not the stronger fixed-annihilator property. -/
theorem support (r : Roots C u w hv) (a b : Fin 3×Fin 5→ℤ)
    (hray : ∀ i,GaussianRayQuadratic318.Ray (row C u w i.1 i.2).natAbs (a i) (b i))
    (ha7 : ∀ i,a i%7=1) (hb7 : ∀ i,b i%7=3)
    (h7 : ∀ i,¬(row C u w i.1 i.2).natAbs∣49)
    (q : ℕ) [Fact q.Prime] (h3 : q%4=3)
    (hc : ∀ i,q∣primaryOrder C u w hv r i ∨ q∣oppositeOrder C u w hv r i) :
    q∣ActualQuadraticCoefficientContent318.content C ∨ q∣Nat.gcd (u-1).natAbs w.natAbs :=
  ActualQuadraticCoefficientContent318.support C u w q
    (fun i => (ActualInertCoverageResidues318.all_residues C u w hv r a b hray ha7 hb7 h7 q h3 hc i).1)
/-- If the SAME tuple has translated primitive defect one, all possible
common inert divisors are in the FIXED coefficient content. Existence of
such a tuple, and even a successful divisor of that content, stays open. -/
theorem content_of_coprime (r : Roots C u w hv) (a b : Fin 3×Fin 5→ℤ)
    (hray : ∀ i,GaussianRayQuadratic318.Ray (row C u w i.1 i.2).natAbs (a i) (b i))
    (ha7 : ∀ i,a i%7=1) (hb7 : ∀ i,b i%7=3)
    (h7 : ∀ i,¬(row C u w i.1 i.2).natAbs∣49)
    (q : ℕ) [Fact q.Prime] (h3 : q%4=3)
    (hc : ∀ i,q∣primaryOrder C u w hv r i ∨ q∣oppositeOrder C u w hv r i)
    (hcop : Nat.Coprime (u-1).natAbs w.natAbs) :
    q∣ActualQuadraticCoefficientContent318.content C := by
  rcases support C u w hv r a b hray ha7 hb7 h7 q h3 hc with hk|hg
  · exact hk
  · rw [hcop.gcd_eq_one] at hg
    exact False.elim ((Fact.out : q.Prime).ne_one (Nat.dvd_one.mp hg))
end ActualInertOrderCoverageSupport318
