module
public import ContactOppositeData318
public import RawSelectedContact318
public section
namespace RawSelectedLeafData318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay RawWeights318
open ConcretePadic318 SourcePadic318 CompressedOrientation318 FiniteContact318
open ContactLeafData318
set_option maxHeartbeats 0
variable (p:ℕ) [Fact p.Prime]

/-- Actual source contact in chain0, with one chosen orientation and every
 decoded leaf, without any supplied split root or scale-finiteness premise. -/
theorem source_selected0 (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (f:ℤ) (j:Fin 5) (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hf:rationalPlace p (t0 S w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    ∃(rho:ℚ_[p])(hr:rho^2=2),0<f-5*padicValRat p (A0 S w) ∧
      (8:WithTop ℤ)≤place p rho hr (fH w) ∧ LeafBounds (place p rho hr) S w := by
  obtain ⟨rho,hr,hm,hor⟩:=RawSelectedContact318.source_contact0_selected p S w source f j hgood hp17 hp41 hf hpos hodd
  rcases hor with hh|hh
  · exact ⟨rho,hr,hm,hh.1,inputs0_bounds _ S w hh.2.2⟩
  · exact ⟨-rho,negative_root p rho hr,hm,hh.1,inputs0_bounds _ S w hh.2.2⟩

/-- Actual source contact in chain1, with one chosen orientation and every
 decoded leaf, without any supplied split root or scale-finiteness premise. -/
theorem source_selected1 (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (f:ℤ) (j:Fin 5) (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hf:rationalPlace p (t1 S w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    ∃(rho:ℚ_[p])(hr:rho^2=2),0<f-5*padicValRat p (A1 S w) ∧
      (8:WithTop ℤ)≤place p rho hr (fH w) ∧ LeafBounds (place p rho hr) S w := by
  obtain ⟨rho,hr,hm,hor⟩:=RawSelectedContact318.source_contact1_selected p S w source f j hgood hp17 hp41 hf hpos hodd
  rcases hor with hh|hh
  · exact ⟨rho,hr,hm,hh.1,inputs1_bounds _ S w hh.2.2⟩
  · exact ⟨-rho,negative_root p rho hr,hm,hh.1,inputs1_bounds _ S w hh.2.2⟩

/-- Actual source contact in chain2, with one chosen orientation and every
 decoded leaf, without any supplied split root or scale-finiteness premise. -/
theorem source_selected2 (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (f:ℤ) (j:Fin 5) (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hf:rationalPlace p (t2 S w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    ∃(rho:ℚ_[p])(hr:rho^2=2),0<f-5*padicValRat p (A2 S w) ∧
      (8:WithTop ℤ)≤place p rho hr (fH w) ∧ LeafBounds (place p rho hr) S w := by
  obtain ⟨rho,hr,hm,hor⟩:=RawSelectedContact318.source_contact2_selected p S w source f j hgood hp17 hp41 hf hpos hodd
  rcases hor with hh|hh
  · exact ⟨rho,hr,hm,hh.1,inputs2_bounds _ S w hh.2.2⟩
  · exact ⟨-rho,negative_root p rho hr,hm,hh.1,inputs2_bounds _ S w hh.2.2⟩

end RawSelectedLeafData318
#print axioms RawSelectedLeafData318.source_selected0
#print axioms RawSelectedLeafData318.source_selected1
#print axioms RawSelectedLeafData318.source_selected2
