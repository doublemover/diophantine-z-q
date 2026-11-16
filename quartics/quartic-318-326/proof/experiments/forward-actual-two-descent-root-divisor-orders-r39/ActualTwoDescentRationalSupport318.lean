module
public import ActualTwoDescentRationalValuationRestrictions318
public section
noncomputable section
namespace ActualTwoDescentRationalSupport318
open ActualTwoDescentRationalPointPlaces318 ActualTwoDescentRationalValuationRestrictions318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actual_outside_prime_not_dvd (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (q : ℕ) (hq : q.Prime) (hout : ∀ i, q ≠ p i) : ¬q ∣ ∏ i, p i := by
  have hc : Nat.Coprime q (∏ i, p i) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro i _
    exact (Nat.coprime_primes hq Fact.out).mpr (hout i)
  intro hd
  exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hc (dvd_refl q) hd)

/-- Actual curve points force all first-coordinate squareclass primes
outside3 and the specified support to occur with even valuation. -/
theorem actual_rational_first_support (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) (P : RationalPoint (∏ i, p i)) :
    ∀ q : ℕ, q.Prime → q ≠ 3 → (∀ i, q ≠ p i) → Even (padicValRat q (P.x+3*(∏ i, p i : ℕ))) := by
  intro q hq hq3 hout
  letI : Fact q.Prime := ⟨hq⟩
  by_cases hq2 : q=2
  · subst q
    have h4 : ((∏ i, p i : ℕ) : ZMod 4)=3 := by
      have h := congrArg (ZMod.castHom (by decide : 4 ∣ 12) (ZMod 4)) hn
      simpa using h
    have hm : (∏ i, p i)%4=3 := by
      have h := congrArg ZMod.val h4
      simpa only [ZMod.val_natCast] using h
    exact (actual_rational_two_valuations _ hm P).2
  · exact (actual_rational_good_valuations q _ hq2 hq3 (actual_outside_prime_not_dvd p q hq hout) P).2

/-- The actual second-coordinate squareclass has NO extra prime3 factor;
the genuine Q3 square theorem removes it, and Q2 parity removes2. -/
theorem actual_rational_second_support (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) (P : RationalPoint (∏ i, p i)) :
    ∀ q : ℕ, q.Prime → (∀ i, q ≠ p i) → Even (padicValRat q (P.x-(∏ i, p i : ℕ))) := by
  intro q hq hout
  letI : Fact q.Prime := ⟨hq⟩
  by_cases hq2 : q=2
  · subst q
    have h4 : ((∏ i, p i : ℕ) : ZMod 4)=3 := by
      have h := congrArg (ZMod.castHom (by decide : 4 ∣ 12) (ZMod 4)) hn
      simpa using h
    have hm : (∏ i, p i)%4=3 := by
      have h := congrArg ZMod.val h4
      simpa only [ZMod.val_natCast] using h
    exact (actual_rational_two_valuations _ hm P).1
  by_cases hq3 : q=3
  · subst q
    have h3 : ((∏ i, p i : ℕ) : ZMod 3)=2 := by
      have h := congrArg (ZMod.castHom (by decide : 3 ∣ 12) (ZMod 3)) hn
      simpa using h
    exact actual_rational_three_second_valuation _ h3 P
  · exact (actual_rational_good_valuations q _ hq2 hq3 (actual_outside_prime_not_dvd p q hq hout) P).1

end ActualTwoDescentRationalSupport318
