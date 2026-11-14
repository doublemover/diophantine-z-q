module
public import ActualTwoDescentRationalPointPlaces318
public section
noncomputable section
namespace ActualTwoDescentRationalValuationRestrictions318
open ActualTwoDescentRationalPointPlaces318 ActualTwoDescentGoodPrimeValuations318
open ActualTwoDescentTwoAdicEvenCoordinates318 ActualTwoDescentThreeAdicSecondSquare318
set_option maxHeartbeats 16000000

lemma actual_rational_good_valuations (q n : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hn : ¬q ∣ n) (P : RationalPoint n) :
    Even (padicValRat q (P.x-n)) ∧ Even (padicValRat q (P.x+3*n)) := by
  have h := (actual_good_prime_valuations n hq2 hq3 hn (toLocal q P)).2
  rwa [actual_rational_minus_valuation,actual_rational_plus_valuation] at h

lemma actual_rational_two_valuations (n : ℕ) (hn : n%4=3) (P : RationalPoint n) :
    Even (padicValRat 2 (P.x-n)) ∧ Even (padicValRat 2 (P.x+3*n)) := by
  have h := actual_two_even_coordinates n hn (toLocal 2 P)
  rwa [actual_rational_minus_valuation,actual_rational_plus_valuation] at h

lemma actual_rational_three_second_valuation (n : ℕ) (hn : (n : ZMod 3)=2)
    (P : RationalPoint n) : Even (padicValRat 3 (P.x-n)) := by
  obtain ⟨r,hr,he⟩ := actual_three_second_square n hn (toLocal 3 P)
  have hv := congrArg Padic.valuation he
  rw [Padic.valuation_pow,actual_rational_minus_valuation] at hv
  exact ⟨r.valuation,by omega⟩

end ActualTwoDescentRationalValuationRestrictions318
