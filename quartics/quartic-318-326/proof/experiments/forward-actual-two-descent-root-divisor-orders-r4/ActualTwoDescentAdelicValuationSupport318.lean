module
public import ActualTwoDescentAdelicPairData318
public section
noncomputable section
namespace ActualTwoDescentAdelicValuationSupport318
set_option maxHeartbeats 16000000

open ActualTwoDescentAdelicPairData318 ActualTwoDescentGoodPrimeValuations318
open ActualTwoDescentTwoAdicEvenCoordinates318 ActualTwoDescentThreeAdicSecondSquare318
open ActualTwoDescentRationalSupport318
open scoped BigOperators

lemma actual_even_of_local_square_multiplier {q : ℕ} [Fact q.Prime]
    (a : ℚ) (ha : a ≠ 0) (x u : ℚ_[q]) (hu : u ≠ 0)
    (hx : x=(a : ℚ_[q])*u^2) (he : Even x.valuation) : Even (padicValRat q a) := by
  rw [hx,Padic.valuation_mul (Rat.cast_ne_zero.mpr ha) (pow_ne_zero _ hu),
    Padic.valuation_pow,Padic.valuation_ratCast] at he
  obtain ⟨k,hk⟩ := he
  exact ⟨k-u.valuation,by omega⟩

lemma actual_adelic_good_parity (q n : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hn : ¬q ∣ n) (A B : ℚ) (H : AdelicPair n A B) :
    Even (padicValRat q A) ∧ Even (padicValRat q B) := by
  obtain ⟨P,u,v,hu,hv,hA,hB⟩ := H.finite_places q
  have he := actual_good_prime_valuations n hq2 hq3 hn P
  exact ⟨actual_even_of_local_square_multiplier A H.first_ne _ u hu hA he.2.2,
    actual_even_of_local_square_multiplier B H.second_ne _ v hv hB he.2.1⟩

lemma actual_adelic_two_parity (n : ℕ) (hn : n%4=3) (A B : ℚ) (H : AdelicPair n A B) :
    Even (padicValRat 2 A) ∧ Even (padicValRat 2 B) := by
  obtain ⟨P,u,v,hu,hv,hA,hB⟩ := H.finite_places 2
  have he := actual_two_even_coordinates n hn P
  exact ⟨actual_even_of_local_square_multiplier A H.first_ne _ u hu hA he.2,
    actual_even_of_local_square_multiplier B H.second_ne _ v hv hB he.1⟩

lemma actual_adelic_three_parity (n : ℕ) (hn : (n : ZMod 3)=2)
    (A B : ℚ) (H : AdelicPair n A B) : Even (padicValRat 3 B) := by
  obtain ⟨P,u,v,hu,hv,hA,hB⟩ := H.finite_places 3
  obtain ⟨s,hs,hS⟩ := actual_three_second_square n hn P
  have he : Even (P.x-(n : ℚ_[3])).valuation := by
    rw [←hS,Padic.valuation_pow]
    exact ⟨s.valuation,by ring⟩
  exact actual_even_of_local_square_multiplier B H.second_ne _ v hv hB he

lemma actual_adelic_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) (A B : ℚ) (H : AdelicPair (∏ i, p i) A B) :
    (∀ q : ℕ, q.Prime → q ≠ 3 → (∀ i, q ≠ p i) → Even (padicValRat q A)) ∧
    (∀ q : ℕ, q.Prime → (∀ i, q ≠ p i) → Even (padicValRat q B)) := by
  have hm : (∏ i, p i)%4=3 := by
    have h4 := congrArg (ZMod.castHom (by decide : 4 ∣ 12) (ZMod 4)) hn
    have h : ((∏ i, p i : ℕ) : ZMod 4)=3 := by simpa using h4
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast] using hv
  have h3 : ((∏ i, p i : ℕ) : ZMod 3)=2 := by
    have h := congrArg (ZMod.castHom (by decide : 3 ∣ 12) (ZMod 3)) hn
    simpa using h
  constructor
  · intro q hq hq3 hout
    letI : Fact q.Prime := ⟨hq⟩
    by_cases hq2 : q=2
    · subst q; exact (actual_adelic_two_parity _ hm A B H).1
    · exact (actual_adelic_good_parity q _ hq2 hq3 (actual_outside_prime_not_dvd p q hq hout) A B H).1
  · intro q hq hout
    letI : Fact q.Prime := ⟨hq⟩
    by_cases hq2 : q=2
    · subst q; exact (actual_adelic_two_parity _ hm A B H).2
    by_cases hq3 : q=3
    · subst q; exact actual_adelic_three_parity _ h3 A B H
    · exact (actual_adelic_good_parity q _ hq2 hq3 (actual_outside_prime_not_dvd p q hq hout) A B H).2

end ActualTwoDescentAdelicValuationSupport318
