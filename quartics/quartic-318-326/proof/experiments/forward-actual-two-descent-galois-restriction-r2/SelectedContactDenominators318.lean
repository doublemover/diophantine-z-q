module
public import ContactPatternSupport318
public section
noncomputable section
namespace SelectedContactDenominators318
open CircuitReplay ConcretePadic318 ActualDetectorFold318
open ContactPrimeForms318 ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ScaledContactWeights318 ScaledDetectorChain318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

/-- Exactly fifteen actual selected-place conditions, with their same source
leaves. Producing them from Gaussian rays and reduction orders remains open;
the interface does not silently assume arbitrary-prime pole constraints. -/
@[expose] def SelectedTrace (q : ℚ) (h u w : ℤ) (hp : Values C u w) : Prop :=
  ∀ j : Fin 3, ∀ i : Fin 5,
    let p := (row C u w j i).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
    3≤p ∧ padicValRat p (denominator C w)=0 ∧
      padicValRat p (delta (ThreeDetectorArithmetic318.scales labels j) (parameter C u w))=0 ∧
    ∃ (rho : ℚ_[p]) (hr : rho^2=2),
      (∀ a∈leaves (view (DetectorGateWitness318.witness q labels h)
        (ThreeDetectorArithmetic318.scales labels j) (parameter C u w)),
        0<place p rho hr (a.1*a.2)) ∧
      (∀ a∈leaves (view (DetectorGateWitness318.witness q labels h)
        (ThreeDetectorArithmetic318.scales labels j) (parameter C u w)),
        ValuationEvenNormChain.OddAt (place p (-rho) (negative_root p rho hr)) a.1 ∧
        ValuationEvenNormChain.EvenAt (place p (-rho) (negative_root p rho hr)) a.2)

/-- The actual trace theorem and complete finite support coverage discharge
all three reduced-denominator square conditions, at the stored values. -/
theorem square_denominators (hn : ∀ j, labels j≠0) (q : ℚ) (h u w : ℤ)
    (hp : Values C u w)
    (hb : ∀ j : Fin 3, 0<ThreeDetectorUniformFamily318.witness q labels h
      (parameter C u w) (190+51*j.val))
    (hs : SelectedTrace C q h u w hp) :
    ∀ j : Fin 3, IsSquare (ThreeDetectorUniformFamily318.witness q labels h
      (parameter C u w) (190+51*j.val)).den := by
  apply ThreeDetectorArithmetic318.stored_square_denominators q labels hn h (u:ℚ)
    (denominator C w) (denominator_ne C w hp.nonzero) (row C u w)
    (linear_eq C u w) (row_ne C u w hp)
    (fun j => (positive_domain C q h u w j (hb j)).1)
    (fun j => (positive_domain C q h u w j (hb j)).2)
  intro j p hprime hpos
  obtain ⟨i,he⟩ := support_selected C u w hp j p hprime hpos
  subst p
  exact hs j i

/-- Small-prime preparation consumes precisely these integer values and the
same parameter, center residue and finalh as the real/CRT source consumer. -/
theorem local_preparation (p : ℕ) [Fact p.Prime] (q : ℚ) (h₀ L h : ℕ) (N A : ℤ)
    (hprepared : SourceLocalProgression318.Prepared p q labels h₀ L N A)
    (u w : ℤ) (hp : Values C u w) (hdepth : N≤padicValRat p (denominator C w))
    (hh : Nat.ModEq L h h₀)
    (hunit : ∀ k∈coefficients C, padicValRat p (value u w k:ℚ)=0)
    (hsquare : ∀ k∈coefficients C, IsSquare (value u w k:ℚ_[p])) :
    ∀ j : Fin 3,
      IsSquare ((ThreeDetectorUniformFamily318.witness q labels (h:ℤ) (parameter C u w)
        (190+51*j.val):ℚ):ℚ_[p]) ∧
      A≤padicValRat p (ThreeDetectorUniformFamily318.witness q labels (h:ℤ)
        (parameter C u w) (190+51*j.val)) := by
  exact hprepared (u:ℚ) (denominator C w) (denominator_ne C w hp.nonzero) hdepth h hh
    (row C u w) (linear_eq C u w) (row_ne C u w hp)
    (fun j i => hunit _ (coefficient_mem C (j,i)))
    (fun j i => hsquare _ (coefficient_mem C (j,i)))

end SelectedContactDenominators318
