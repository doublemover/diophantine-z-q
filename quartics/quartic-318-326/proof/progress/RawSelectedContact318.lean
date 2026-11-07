module
public import FiniteScale318
public section
namespace RawSelectedContact318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay RawDetector318 RawWeights318
open SourceContact318 SourcePadic318 ConcretePadic318 FiniteContact318 CompressedOrientation318
set_option maxHeartbeats 0
variable (p:ℕ) [Fact p.Prime]

/-- Fully source-linked finite contact selection in chain 0. Both local-place
existence and finiteness of the scale valuation are derived, not assumed. -/
theorem source_contact0_selected
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hf : rationalPlace p (t0 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    ∃ (rho : ℚ_[p]) (hr : rho^2=2),
    0<f-5*padicValRat p (A0 S w) ∧
    (((8:WithTop ℤ)≤place p rho hr (fH w) ∧ place p (-rho) (negative_root p rho hr) (fH w)=0 ∧
      (∀x∈inputs0 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1)) ∨
    ((8:WithTop ℤ)≤place p (-rho) (negative_root p rho hr) (fH w) ∧ place p rho hr (fH w)=0 ∧
      (∀x∈inputs0 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1))) := by
  exact InertSelectedContact318.source_contact0_selected p S w source
    (padicValRat p (A0 S w)) f j hgood hp17 hp41
    (rational_value p _ (FiniteScale318.A0_ne_zero S w)) hf hpos hodd

/-- Fully source-linked finite contact selection in chain 1. Both local-place
existence and finiteness of the scale valuation are derived, not assumed. -/
theorem source_contact1_selected
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hf : rationalPlace p (t1 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    ∃ (rho : ℚ_[p]) (hr : rho^2=2),
    0<f-5*padicValRat p (A1 S w) ∧
    (((8:WithTop ℤ)≤place p rho hr (fH w) ∧ place p (-rho) (negative_root p rho hr) (fH w)=0 ∧
      (∀x∈inputs1 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1)) ∨
    ((8:WithTop ℤ)≤place p (-rho) (negative_root p rho hr) (fH w) ∧ place p rho hr (fH w)=0 ∧
      (∀x∈inputs1 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1))) := by
  exact InertSelectedContact318.source_contact1_selected p S w source
    (padicValRat p (A1 S w)) f j hgood hp17 hp41
    (rational_value p _ (FiniteScale318.A1_ne_zero S w source)) hf hpos hodd

/-- Fully source-linked finite contact selection in chain 2. Both local-place
existence and finiteness of the scale valuation are derived, not assumed. -/
theorem source_contact2_selected
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hf : rationalPlace p (t2 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    ∃ (rho : ℚ_[p]) (hr : rho^2=2),
    0<f-5*padicValRat p (A2 S w) ∧
    (((8:WithTop ℤ)≤place p rho hr (fH w) ∧ place p (-rho) (negative_root p rho hr) (fH w)=0 ∧
      (∀x∈inputs2 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1)) ∨
    ((8:WithTop ℤ)≤place p (-rho) (negative_root p rho hr) (fH w) ∧ place p rho hr (fH w)=0 ∧
      (∀x∈inputs2 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1))) := by
  exact InertSelectedContact318.source_contact2_selected p S w source
    (padicValRat p (A2 S w)) f j hgood hp17 hp41
    (rational_value p _ (FiniteScale318.A2_ne_zero S w source)) hf hpos hodd

end RawSelectedContact318

#print axioms RawSelectedContact318.source_contact0_selected

#print axioms RawSelectedContact318.source_contact1_selected

#print axioms RawSelectedContact318.source_contact2_selected
