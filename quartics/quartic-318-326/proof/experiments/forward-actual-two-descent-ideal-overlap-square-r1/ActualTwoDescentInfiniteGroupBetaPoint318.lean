module
public import ActualTwoDescentInfiniteGroupCardinality318
public section
noncomputable section
namespace ActualTwoDescentInfiniteGroupBetaPoint318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentActualQuotientControl318
open ActualTwoDescentInfiniteGroupCardinality318 ActualTwoDescentPointExtraction318
open ActualTwoDescentRationalHeightDescent318

/-- A genuine infinitude theorem for the ACTUAL original rational curve is
now sufficient for its retained beta point. No Selmer/local count replaces it. -/
theorem actual_beta_point_of_infinite (n b : ℕ) (hn : n ≠ 0)
    (C : QuotientControl n b) (hInfinite : Infinite (Point (n : ℚ))) :
    Nonempty (KummerPoint (b : ℚ) (n : ℚ)) :=
  C.2.2.2 (actual_quotient_eight_of_infinite (n : ℚ) (by exact_mod_cast hn) C.2.1 C.2.2.1 hInfinite)

/-- The finite-generation part is produced unconditionally by the constructed
arithmetic data; actual rational infinitude remains a separate global input. -/
theorem actual_control_finite_generation (n b : ℕ) (hn : n ≠ 0) (C : QuotientControl n b) :
    AddGroup.FG (Point (n : ℚ)) ∧ Finite (AddCommGroup.torsion (Point (n : ℚ))) :=
  ⟨actual_finite_generation (n : ℚ) (by exact_mod_cast hn) C.2.1,
   actual_rational_torsion_finite (n : ℚ) (by exact_mod_cast hn)⟩

end ActualTwoDescentInfiniteGroupBetaPoint318
