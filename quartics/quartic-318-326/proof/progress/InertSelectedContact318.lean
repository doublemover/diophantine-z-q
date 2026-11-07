module
public import InertHensel318
public import SelectedContact318
public section
namespace InertSelectedContact318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay RawDetector318 RawWeights318
open SourceContact318 SourcePadic318 ConcretePadic318 FiniteContact318 CompressedOrientation318
set_option maxHeartbeats 0
variable (p:ℕ) [Fact p.Prime]

/-- Literal chain 0 now yields an actual selected p-adic place and all
sixteen source leaf bounds. No square root or local-place existence premise. -/
theorem source_contact0_selected
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hA : rationalPlace p (A0 S w)=a)
    (hf : rationalPlace p (t0 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    ∃ (rho : ℚ_[p]) (hr : rho^2=2),
    0<f-5*a ∧
    (((8:WithTop ℤ)≤place p rho hr (fH w) ∧ place p (-rho) (negative_root p rho hr) (fH w)=0 ∧
      (∀x∈inputs0 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1)) ∨
    ((8:WithTop ℤ)≤place p (-rho) (negative_root p rho hr) (fH w) ∧ place p rho hr (fH w)=0 ∧
      (∀x∈inputs0 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1))) := by
  obtain ⟨rho,hr⟩ := InertHensel318.source_contact0_padic_split p S w source a f j
    hgood hp17 hp41 hA hf hpos hodd
  exact ⟨rho,hr,SelectedContact318.source_contact0_selected p rho hr S w source a f j
    hgood hp17 hp41 hA hf hpos hodd⟩

/-- Literal chain 1 now yields an actual selected p-adic place and all
sixteen source leaf bounds. No square root or local-place existence premise. -/
theorem source_contact1_selected
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hA : rationalPlace p (A1 S w)=a)
    (hf : rationalPlace p (t1 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    ∃ (rho : ℚ_[p]) (hr : rho^2=2),
    0<f-5*a ∧
    (((8:WithTop ℤ)≤place p rho hr (fH w) ∧ place p (-rho) (negative_root p rho hr) (fH w)=0 ∧
      (∀x∈inputs1 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1)) ∨
    ((8:WithTop ℤ)≤place p (-rho) (negative_root p rho hr) (fH w) ∧ place p rho hr (fH w)=0 ∧
      (∀x∈inputs1 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1))) := by
  obtain ⟨rho,hr⟩ := InertHensel318.source_contact1_padic_split p S w source a f j
    hgood hp17 hp41 hA hf hpos hodd
  exact ⟨rho,hr,SelectedContact318.source_contact1_selected p rho hr S w source a f j
    hgood hp17 hp41 hA hf hpos hodd⟩

/-- Literal chain 2 now yields an actual selected p-adic place and all
sixteen source leaf bounds. No square root or local-place existence premise. -/
theorem source_contact2_selected
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hA : rationalPlace p (A2 S w)=a)
    (hf : rationalPlace p (t2 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    ∃ (rho : ℚ_[p]) (hr : rho^2=2),
    0<f-5*a ∧
    (((8:WithTop ℤ)≤place p rho hr (fH w) ∧ place p (-rho) (negative_root p rho hr) (fH w)=0 ∧
      (∀x∈inputs2 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1)) ∨
    ((8:WithTop ℤ)≤place p (-rho) (negative_root p rho hr) (fH w) ∧ place p rho hr (fH w)=0 ∧
      (∀x∈inputs2 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1))) := by
  obtain ⟨rho,hr⟩ := InertHensel318.source_contact2_padic_split p S w source a f j
    hgood hp17 hp41 hA hf hpos hodd
  exact ⟨rho,hr,SelectedContact318.source_contact2_selected p rho hr S w source a f j
    hgood hp17 hp41 hA hf hpos hodd⟩

end InertSelectedContact318

#print axioms InertSelectedContact318.source_contact0_selected

#print axioms InertSelectedContact318.source_contact1_selected

#print axioms InertSelectedContact318.source_contact2_selected
