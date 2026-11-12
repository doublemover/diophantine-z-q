module
public import ActualTwoDescentSignedLocalTranslation318
public section
noncomputable section
namespace ActualTwoDescentSignedLocalNormalization318
open ActualTwoDescentSignedLocalTranslation318 ActualTwoDescentSignedRepresentativeTransport318
open ActualTwoDescentSignedComparisons318 ActualTwoDescentRepresentedSupport318
open ActualTwoDescentCoordinateSymbols318 ActualTwoDescentPrimeMonomials318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

lemma actual_signed_zero_iff (q : ℕ) [Fact q.Prime] (p : Option U → ℕ)
    (δ : ZMod 2) (u v : Option U → ZMod 2) :
    SignedRepresentedAt q p 0 δ u v ↔
      RepresentedAt q (∏ i, p i) (firstRepresentative p δ u) (monomial p v) := by
  simp only [SignedRepresentedAt,RepresentedAt,signedSecond,ZMod.val_zero,pow_zero,
    one_mul,Int.cast_natCast]

/-- Normalization by the ACTUAL rational two-torsion point, in both
directions, at every completed field including2 and3. -/
theorem actual_signed_local_normalization (q : ℕ) [Fact q.Prime]
    (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (ε δ : ZMod 2) (u v : Option U → ZMod 2) :
    SignedRepresentedAt q p ε δ u v ↔
      RepresentedAt q (∏ i, p i) (firstRepresentative p (δ+ε) u) (monomial p (toggle ε v)) := by
  fin_cases ε
  · simpa only [add_zero,toggle,zero_smul,add_zero] using actual_signed_zero_iff q p δ u v
  · constructor
    · intro H
      have h := actual_signed_local_translation q p 1 δ u v H
      have h0 : SignedRepresentedAt q p 0 (δ+1) u (toggle 1 v) := by simpa using h
      exact (actual_signed_zero_iff q p _ _ _).mp h0
    · intro H
      have h0 := (actual_signed_zero_iff q p (δ+1) u (toggle 1 v)).mpr H
      have h := actual_signed_local_translation q p 0 (δ+1) u (toggle 1 v) h0
      simpa only [zero_add,bit_toggle_twice,toggle_twice] using h

end ActualTwoDescentSignedLocalNormalization318
