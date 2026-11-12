module
public import ActualScreenedInertCoverageSupport318
public section
noncomputable section
namespace ActualFullScreenInertCoverageObstruction318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 GaussianFiniteCoordinateCRT318
open GaussianFixedClassPrimeNormSource318
variable {labels : Fin 4→ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- A growing FREE-coordinate screen through the actual coefficient/step
bound (apart from7, handled by its historical ray) excludes common
INERT-divisor coverage entirely. This is a strategy
obstruction, not nonexistence of compatible tuples or of split-divisor
coverage. The screen depends on the very same pair, not a fixed-class limit. -/
theorem no_coverage {S : Finset ℕ} (d : Class S) (z : (Fin 3×Fin 5)→ℤ×ℤ)
    (hn : ∀ i,((row C u w i.1 i.2).natAbs:ℤ)=
      (translated d (z i)).1^2+(translated d (z i)).2^2)
    (h7 : ∀ i : Fin 3×Fin 5,¬(row C u w i.1 i.2).natAbs∣49)
    (j : Fin 3×Fin 5) (hj : C.coefficient j≠0)
    (hS : ∀ q : ℕ,q.Prime→q%4=3→q≠7→q≤max (C.coefficient j).natAbs w.natAbs→q∈S)
    (r : Roots C u w hv) (q : ℕ) [Fact q.Prime] (h3 : q%4=3) :
    ¬(∀ i,q∣primaryOrder C u w hv r i ∨ q∣oppositeOrder C u w hv r i) := by
  intro hc
  let a : Fin 3×Fin 5→ℤ := fun i => (translated d (z i)).1
  let b : Fin 3×Fin 5→ℤ := fun i => (translated d (z i)).2
  have hray (i : Fin 3×Fin 5) : GaussianRayQuadratic318.Ray
      (row C u w i.1 i.2).natAbs (a i) (b i) :=
    ⟨hn i,(full_ray d (z i)).1,(full_ray d (z i)).2.1⟩
  have ha7 : ∀ i,a i%7=1 := fun i => (full_ray d (z i)).2.2.1
  have hb7 : ∀ i,b i%7=3 := fun i => (full_ray d (z i)).2.2.2
  have hres:=ActualInertCoverageResidues318.all_residues C u w hv r a b hray ha7 hb7 h7 q h3 hc
  have hbound:=ActualQuadraticCoefficientContent318.bounded C u w hv.nonzero q
    (fun i => (hres i).1) j hj
  have hq7 : q≠7 := by
    intro he
    have hz : (b (0,0):ZMod 7)=0 := by simpa only [he] using (hres (0,0)).2
    obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (b (0,0)) 7).mp hz
    have hb:=hb7 (0,0)
    omega
  have hqS:=hS q Fact.out h3 hq7 hbound
  let i : Fin 3×Fin 5 := (0,0)
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
  have hq2 : q≠2 := by omega
  rcases hc i with hm|hp
  · exact SelectedGaussianCRTDivisorExclusion318.translated_excludes p (r i).val
      (r i).property d (z i) (hn i) (h7 i) q hqS Fact.out hq2 hm
  · exact SelectedGaussianCRTDivisorExclusion318.translated_excludes p (-(r i).val)
      (ConcretePadic318.negative_root p _ _) d (z i) (hn i) (h7 i) q hqS Fact.out hq2 hp
end ActualFullScreenInertCoverageObstruction318
