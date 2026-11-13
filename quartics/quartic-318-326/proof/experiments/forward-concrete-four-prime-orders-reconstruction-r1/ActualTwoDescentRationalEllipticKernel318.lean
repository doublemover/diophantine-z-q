module
public import ActualTwoDescentTranslationGroupLaw318
public section
noncomputable section
namespace ActualTwoDescentRationalEllipticKernel318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentRationalPointPlaces318
open ActualTwoDescentIdentityClassKernel318 ActualTwoDescentTorsionSquarePairs318
open ActualTwoDescentTranslationGroupLaw318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentTorsionTranslation318

/-- The original rational point data embeds in the actual rational elliptic group. -/
def rationalEllipticPoint (n : ℕ) (hn : n ≠ 0) (P : RationalPoint n) : Point (n : ℚ) :=
  point (n : ℚ) P.x P.y (by exact_mod_cast hn) P.curve

/-- Identity Kummer class if and only if the SAME original rational point
is twice an actual rational elliptic point. -/
theorem actual_rational_identity_kernel (n : ℕ) (hn : n ≠ 0) (P : RationalPoint n) :
    SquarePair (P.x+3*n) (P.x-n) 1 1 ↔
      ∃ Q : Point (n : ℚ), Q+Q=rationalEllipticPoint n hn P := by
  exact actual_identity_class_iff_double (n : ℚ) P.x P.y (by exact_mod_cast hn)
    P.x_ne P.minus_ne P.plus_ne P.curve

/-- Rational torsion translation uses this same embedding and group law. -/
theorem actual_rational_translation_group (n : ℕ) (hn : n ≠ 0) (P : RationalPoint n) :
    rationalEllipticPoint n hn P+torsionPoint (n : ℚ) (by exact_mod_cast hn)=
      point (n : ℚ) (translatedX (n : ℚ) P.x) (translatedY (n : ℚ) P.x P.y)
        (by exact_mod_cast hn) (translated_curve (n : ℚ) P.x P.y P.plus_ne P.curve) :=
  actual_translation_is_addition (n : ℚ) P.x P.y (by exact_mod_cast hn) P.plus_ne P.curve

end ActualTwoDescentRationalEllipticKernel318
