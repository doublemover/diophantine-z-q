module
public import ActualTwoDescentSignedLocalNormalization318
public section
noncomputable section
namespace ActualTwoDescentSignedRealNormalization318
open ActualTwoDescentSignedRepresentativeTransport318 ActualTwoDescentSignedComparisons318
open ActualTwoDescentTorsionTranslation318 ActualTwoDescentTranslatedSquarePair318
open ActualTwoDescentTorsionSquarePairs318 ActualTwoDescentArchimedeanRepresentation318
open ActualTwoDescentCoordinateSymbols318 ActualTwoDescentPrimeMonomials318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

def SignedRealRepresented (p : Option U → ℕ) (ε δ : ZMod 2) (u v : Option U → ZMod 2) : Prop :=
  ∃ x y : ℝ, x ≠ 0 ∧ x-(∏ i, p i : ℕ) ≠ 0 ∧ x+3*(∏ i, p i : ℕ) ≠ 0 ∧
    y^2=x*(x-(∏ i, p i : ℕ))*(x+3*(∏ i, p i : ℕ)) ∧
    SquarePair (x+3*(∏ i, p i : ℕ)) (x-(∏ i, p i : ℕ))
      (firstRepresentative p δ u : ℝ) (signedSecond p ε v : ℝ)

lemma actual_signed_real_zero_iff (p : Option U → ℕ) (δ : ZMod 2) (u v : Option U → ZMod 2) :
    SignedRealRepresented p 0 δ u v ↔
      RealRepresented (∏ i, p i) (firstRepresentative p δ u) (monomial p v) := by
  simp only [SignedRealRepresented,RealRepresented,SquarePair,signedSecond,ZMod.val_zero,
    pow_zero,one_mul,Int.cast_natCast]
  constructor
  · rintro ⟨x,y,hx,hB,hA,hc,r,s,hr,hs,heA,heB⟩
    exact ⟨x,y,r,s,hx,hB,hA,hr,hs,hc,heA,heB⟩
  · rintro ⟨x,y,r,s,hx,hB,hA,hr,hs,hc,heA,heB⟩
    exact ⟨x,y,hx,hB,hA,hc,r,s,hr,hs,heA,heB⟩

theorem actual_signed_real_translation (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (ε δ : ZMod 2) (u v : Option U → ZMod 2) (H : SignedRealRepresented p ε δ u v) :
    SignedRealRepresented p (ε+1) (δ+1) u (toggle 1 v) := by
  obtain ⟨x,y,hx,hB,hA,hc,HP⟩ := H
  have hn0 : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => (Fact.out : (p i).Prime).ne_zero)
  have hnc : ((∏ i, p i : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have Hn := translated_nonzero (∏ i, p i : ℕ) x hnc hx hB hA
  refine ⟨translatedX (∏ i, p i : ℕ) x,translatedY (∏ i, p i : ℕ) x y,
    Hn.1,Hn.2.1,Hn.2.2,translated_curve _ x y hA hc,?_⟩
  have ht := actual_translated_square_pair (∏ i, p i : ℕ) x y
    (firstRepresentative p δ u : ℝ) (signedSecond p ε v : ℝ) hnc hx hB hA hc HP
  exact actual_pair_rescale _ _ _ _ _ _ ((3 : ℝ)^δ.val) (monomial p v : ℝ)
    (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (monomial_pos p v).ne')
    (actual_first_torsion_transport p δ u) (actual_second_torsion_transport p ε v) ht

/-- Real signed normalization uses the SAME actual rational point map as
all finite primes, including the correct original-coordinate signs. -/
theorem actual_signed_real_normalization (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (ε δ : ZMod 2) (u v : Option U → ZMod 2) :
    SignedRealRepresented p ε δ u v ↔
      RealRepresented (∏ i, p i) (firstRepresentative p (δ+ε) u) (monomial p (toggle ε v)) := by
  fin_cases ε
  · simpa only [add_zero,toggle,zero_smul,add_zero] using actual_signed_real_zero_iff p δ u v
  · constructor
    · intro H
      have h := actual_signed_real_translation p 1 δ u v H
      have h0 : SignedRealRepresented p 0 (δ+1) u (toggle 1 v) := by simpa using h
      exact (actual_signed_real_zero_iff p _ _ _).mp h0
    · intro H
      have h0 := (actual_signed_real_zero_iff p (δ+1) u (toggle 1 v)).mpr H
      have h := actual_signed_real_translation p 0 (δ+1) u (toggle 1 v) h0
      simpa only [zero_add,bit_toggle_twice,toggle_twice] using h

end ActualTwoDescentSignedRealNormalization318
