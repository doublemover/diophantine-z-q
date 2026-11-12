module
public import QuadraticPatternUnitResidues318
public section
noncomputable section
namespace ActualInertCoverageResidues318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318
variable {labels : Fin 4→ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- NECESSARY congruences for coverage by an inert auxiliary prime q.
The selected curve primes p vary; q is NOT one of those primes. Repeated
original positions and BOTH root choices are retained. -/
theorem all_residues (r : Roots C u w hv) (a b : Fin 3×Fin 5→ℤ)
    (hray : ∀ i,GaussianRayQuadratic318.Ray (row C u w i.1 i.2).natAbs (a i) (b i))
    (ha7 : ∀ i,a i%7=1) (hb7 : ∀ i,b i%7=3)
    (h7 : ∀ i,¬(row C u w i.1 i.2).natAbs∣49)
    (q : ℕ) [Fact q.Prime] (h3 : q%4=3)
    (hc : ∀ i,q∣primaryOrder C u w hv r i ∨ q∣oppositeOrder C u w hv r i) :
    ∀ i,(row C u w i.1 i.2:ZMod q)=1 ∧ (b i:ZMod q)=0 := by
  intro i
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
  have he : (p:ℤ)=row C u w i.1 i.2 := by
    exact (Int.natCast_natAbs _).trans (abs_of_pos (row_pos C u w hv i.1 i.2))
  have heq : (p:ZMod q)=(row C u w i.1 i.2:ZMod q) := by exact_mod_cast he
  have hs : (p:ZMod q)=1 ∧ (b i:ZMod q)=0 := by
    rcases hc i with hm|hp
    · exact SelectedGaussianOrderPrimeSupport318.inert p (r i).val (r i).property
        (a i) (b i) (hray i) (ha7 i) (hb7 i) (h7 i) q h3 hm
    · exact SelectedGaussianOrderPrimeSupport318.inert p (-(r i).val)
        (ConcretePadic318.negative_root p _ _) (a i) (b i) (hray i)
        (ha7 i) (hb7 i) (h7 i) q h3 hp
  exact ⟨heq.symm.trans hs.1,hs.2⟩
end ActualInertCoverageResidues318
