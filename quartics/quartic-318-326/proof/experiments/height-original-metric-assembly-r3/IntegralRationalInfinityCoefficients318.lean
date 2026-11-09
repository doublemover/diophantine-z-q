module
public import IntegralRationalInfinityMap318
public import IntegralGlobalBicanonicalPair318
public import ContactBicanonicalCoefficients318
public section
noncomputable section
namespace IntegralRationalInfinityCoefficients318
open Polynomial IntegralInfinityOriginalField318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

theorem coordinate :
    rationalOrderEquiv c (IntegralInfinityChart318.coordinate ℚ c) =
      ContactFrameNormalization318.infinityCoordinate c :=
  rationalOrderEquiv_polynomial c X

/-- Equality of presentations preserves the actual localized inverse, not
just its value after embedding into a field. -/
theorem presentation_inverse {a b : Fin 3 → ℚ[X]} (h : a=b) :
    presentationEquiv h
      (algebraMap (Localization.Away (∏ j : Fin 3,a j)) (Presentation a)
        (IsLocalization.Away.invSelf (∏ j : Fin 3,a j))) =
    algebraMap (Localization.Away (∏ j : Fin 3,b j)) (Presentation b)
      (IsLocalization.Away.invSelf (∏ j : Fin 3,b j)) := by
  subst b
  all_goals rfl

theorem inverseDenominator :
    rationalOrderEquiv c (IntegralInfinityChart318.inverseDenominator ℚ c) =
      ContactBicanonicalCoefficients318.infinityDenominatorInverse c :=
  presentation_inverse (funext (IntegralInfinityCoefficients318.rational_coefficient c))

theorem scale (k : ℕ) :
    (4 : InfinityOpenChart318.OpenOrder c) *
      algebraMap ℚ (InfinityOpenChart318.OpenOrder c) (∏ j : Fin 3,(c j.succ : ℚ)) *
      (algebraMap ℚ (InfinityOpenChart318.OpenOrder c) (↑(c 0)⁻¹ : ℚ))^k =
    algebraMap ℚ (InfinityOpenChart318.OpenOrder c)
      (ContactBicanonicalCoefficients318.infinityScale c k : ℚ) := by
  simp only [ContactBicanonicalCoefficients318.infinityScale,
    ContactBicanonicalCoefficients318.infinityTwist,ContactBicanonicalCoefficients318.fourUnit,
    Units.val_mul,Units.val_pow_eq_pow_val,Units.coe_prod,Units.val_mk0,map_mul,map_pow,map_ofNat]

theorem coefficient0 :
    rationalOrderEquiv c (IntegralInfinityCoefficients318.coefficient0 ℚ c) =
      ContactBicanonicalCoefficients318.infinityQ0 c := by
  simp only [IntegralInfinityCoefficients318.coefficient0,map_mul,map_pow,map_ofNat,
    IntegralInfinityCoefficients318.otherTwists,IntegralInfinityCoefficients318.k0,
    AlgEquiv.commutes,coordinate,inverseDenominator]
  rw [scale]
  all_goals rfl

theorem coefficient1 :
    rationalOrderEquiv c (IntegralInfinityCoefficients318.coefficient1 ℚ c) =
      ContactBicanonicalCoefficients318.infinityQ1 c := by
  simp only [IntegralInfinityCoefficients318.coefficient1,map_mul,map_pow,map_ofNat,
    IntegralInfinityCoefficients318.otherTwists,IntegralInfinityCoefficients318.k0,
    AlgEquiv.commutes,inverseDenominator]
  rw [scale]
  all_goals rfl

theorem scaled_coefficient (n : Fin 2) :
    rationalOrderEquiv c (IntegralGlobalBicanonicalPair318.infinityCoefficient ℚ c n) =
      (VerticalSection318.J : InfinityOpenChart318.OpenOrder c)^2 *
        (if n=0 then ContactBicanonicalCoefficients318.infinityQ0 c
          else ContactBicanonicalCoefficients318.infinityQ1 c) := by
  by_cases hn : n=0
  · simp only [IntegralGlobalBicanonicalPair318.infinityCoefficient,hn,ite_true,
      map_mul,map_pow,map_intCast,coefficient0]
  · simp only [IntegralGlobalBicanonicalPair318.infinityCoefficient,hn,ite_false,
      map_mul,map_pow,map_intCast,coefficient1]

theorem differential :
    AlgHomDifferential318.map (rationalOrderEquiv c).toAlgHom
      (KaehlerDifferential.D ℚ (IntegralInfinityChart318.Order ℚ c)
        (IntegralInfinityChart318.coordinate ℚ c)) =
      KaehlerDifferential.D ℚ (InfinityOpenChart318.OpenOrder c)
        (ContactFrameNormalization318.infinityCoordinate c) := by
  rw [AlgHomDifferential318.map_D,coordinate]
end IntegralRationalInfinityCoefficients318
