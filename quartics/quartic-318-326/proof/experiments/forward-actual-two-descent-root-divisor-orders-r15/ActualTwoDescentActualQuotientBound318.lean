module
public import ActualTwoDescentRationalKummerImageBound318
public section
noncomputable section
namespace ActualTwoDescentActualQuotientBound318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentEightClassCube318
open ActualTwoDescentSameRationalBounds318 ActualTwoDescentRationalKummerImageBound318

/-- Every actual E(Q)/2E(Q) class maps into the same finite cube. -/
theorem actual_quotient_cube (n b : ℕ) (hn : n ≠ 0) (hb : b ≠ 0)
    (H : RationalEightBound n b) (q : DoubleQuotient (n : ℚ)) :
    ∃ v : Cube, ellipticKummerInjection (n : ℚ) (by exact_mod_cast hn) q=
      cubeClass (n : ℚ) (b : ℚ) (by exact_mod_cast hn) (by exact_mod_cast hb) v := by
  refine QuotientGroup.induction_on q ?_
  intro P
  exact actual_rational_image_bound n b hn hb H P.toAdd

/-- An actual injection into the eight-element cube, not merely a count of
formal local signatures. -/
def quotientCubeEmbedding (n b : ℕ) (hn : n ≠ 0) (hb : b ≠ 0)
    (H : RationalEightBound n b) : DoubleQuotient (n : ℚ) ↪ Cube where
  toFun q := Classical.choose (actual_quotient_cube n b hn hb H q)
  inj' q r he := by
    apply actual_elliptic_kummer_injective (n : ℚ) (by exact_mod_cast hn)
    rw [Classical.choose_spec (actual_quotient_cube n b hn hb H q),
      Classical.choose_spec (actual_quotient_cube n b hn hb H r),he]

/-- The actual rational elliptic quotient is finite and has at most eight elements. -/
theorem actual_quotient_finite_bound (n b : ℕ) (hn : n ≠ 0) (hb : b ≠ 0)
    (H : RationalEightBound n b) : Finite (DoubleQuotient (n : ℚ)) ∧ Nat.card (DoubleQuotient (n : ℚ)) ≤ 8 := by
  let f := quotientCubeEmbedding n b hn hb H
  refine ⟨Finite.of_injective f f.injective,?_⟩
  exact (Nat.card_le_card_of_injective f f.injective).trans_eq cube_card

end ActualTwoDescentActualQuotientBound318
