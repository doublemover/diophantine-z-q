module
public import SelectedGaussianCRTDivisorExclusion318
public section
noncomputable section
namespace ActualScreenedInertCoverageSupport318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 ActualGaussianScreenedSourceData318
variable {labels : Fin 4→ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- Literal old bounded Gaussian source consumption. The simultaneous
Values and the SAME global Data remain inputs. Local completed roots do
not supply those integer coordinates. All fifteen positions use the old
merged-to-position map, so repeated coefficients cannot evade the test. -/
theorem necessary (B Y L : ℕ) (d : Data C B Y L (u,w)) (r : Roots C u w hv)
    (h7 : ∀ i : Fin 3×Fin 5,¬(row C u w i.1 i.2).natAbs∣49)
    (q : ℕ) [Fact q.Prime] (h3 : q%4=3)
    (hc : ∀ i,q∣primaryOrder C u w hv r i ∨ q∣oppositeOrder C u w hv r i) :
    q≠7 ∧ (q∣ActualQuadraticCoefficientContent318.content C ∨
      q∣Nat.gcd (u-1).natAbs w.natAbs) := by
  let a : Fin 3×Fin 5→ℤ := fun i => d.generators.1.1 (position C i)
  let b : Fin 3×Fin 5→ℤ := fun i => d.generators.1.2 (position C i)
  have hray (i : Fin 3×Fin 5) : GaussianRayQuadratic318.Ray
      (row C u w i.1 i.2).natAbs (a i) (b i) := by
    refine ⟨?_,d.a16 (position C i),d.b16 (position C i)⟩
    rw [Int.natCast_natAbs,abs_of_pos (row_pos C u w hv i.1 i.2)]
    exact (d.generators.2.1 (position C i)).symm
  have ha7 : ∀ i,a i%7=1 := fun i => d.a7 (position C i)
  have hb7 : ∀ i,b i%7=3 := fun i => d.b7 (position C i)
  refine ⟨?_,ActualInertOrderCoverageSupport318.support C u w hv r a b hray ha7 hb7 h7 q h3 hc⟩
  intro he
  subst q
  have hz:=(ActualInertCoverageResidues318.all_residues C u w hv r a b hray ha7 hb7 h7
    7 (by decide) hc (0,0)).2
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (b (0,0)) 7).mp hz
  have hb:=hb7 (0,0)
  omega
end ActualScreenedInertCoverageSupport318
