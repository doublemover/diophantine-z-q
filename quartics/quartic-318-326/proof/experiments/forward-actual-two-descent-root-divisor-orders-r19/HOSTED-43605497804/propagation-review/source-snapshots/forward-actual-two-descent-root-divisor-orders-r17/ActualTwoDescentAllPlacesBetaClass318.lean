module
public import ActualTwoDescentLocalPointImageBridge318
public section
noncomputable section
namespace ActualTwoDescentAllPlacesBetaClass318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentTorsionKummerValues318 ActualTwoDescentSquareClassFieldMap318
open ActualTwoDescentAllPlacesIntersection318 ActualTwoDescentLocalKummerWitness318
open ActualTwoDescentLocalPointImageBridge318 ActualTwoDescentGoodPrimeKummerSurjectivity318

lemma actual_rational_beta_map {K : Type*} [Field K] [CharZero K] (β : ℕ) (hβ : β ≠ 0) :
    squarePairMap (algebraMap ℚ K) (retainedBetaClass (β : ℚ) (Nat.cast_ne_zero.mpr hβ))=
      retainedBetaClass (β : K) (Nat.cast_ne_zero.mpr hβ) := by
  apply Prod.ext
  · change squareClassMap (algebraMap ℚ K) (ActualTwoDescentSquareClassQuotient318.classOf (β : ℚ) _)=
      ActualTwoDescentSquareClassQuotient318.classOf (β : K) _
    rw [actual_squareclass_map_value]
    simp only [map_natCast]
  · change squareClassMap (algebraMap ℚ K) 1=1
    exact map_one _

/-- With genuine points at the finitely many bad places, beta is proved to lie
in the ACTUAL all-place intersection. The good-prime clauses are constructed here. -/
theorem actual_all_places_beta (n β : ℕ) (hn : n ≠ 0) (hβ : β ≠ 0) (hdiv : β ∣ n)
    (h2 : Nonempty (LocalKummerPoint (p:=2) β n))
    (h3 : Nonempty (LocalKummerPoint (p:=3) β n))
    (hsupport : ∀ (p : ℕ) [Fact p.Prime], p ∣ n → Nonempty (LocalKummerPoint (p:=p) β n)) :
    retainedBetaClass (β : ℚ) (Nat.cast_ne_zero.mpr hβ) ∈
      allPlacesImage (n : ℚ) (Nat.cast_ne_zero.mpr hn) := by
  apply (actual_all_places_iff _ _ _).mpr
  constructor
  · obtain ⟨P,hP⟩ := actual_real_beta_image n β hn hβ
    simpa only [map_natCast,actual_rational_beta_map] using (show ∃ P : Point (n : ℝ),
      kummerClass (n : ℝ) (Nat.cast_ne_zero.mpr hn) P=retainedBetaClass (β : ℝ) (Nat.cast_ne_zero.mpr hβ) from ⟨P,hP⟩)
  · intro p hp
    letI : DecidableEq (ℚ_[p]) := Classical.decEq _
    have H : ∃ P : Point (n : ℚ_[p]), kummerClass (n : ℚ_[p]) (Nat.cast_ne_zero.mpr hn) P=
        retainedBetaClass (β : ℚ_[p]) (Nat.cast_ne_zero.mpr hβ) := by
      by_cases hp2 : p=2
      · subst p
        exact actual_local_point_kummer_image n β hn hβ (Classical.choice h2)
      by_cases hp3 : p=3
      · subst p
        exact actual_local_point_kummer_image n β hn hβ (Classical.choice h3)
      by_cases hpn : p ∣ n
      · exact actual_local_point_kummer_image n β hn hβ (Classical.choice (hsupport p hpn))
      · exact actual_good_prime_beta_image hp2 hp3 n β hpn (fun hpβ => hpn (dvd_trans hpβ hdiv))
    simpa only [map_natCast,actual_rational_beta_map] using H

end ActualTwoDescentAllPlacesBetaClass318
