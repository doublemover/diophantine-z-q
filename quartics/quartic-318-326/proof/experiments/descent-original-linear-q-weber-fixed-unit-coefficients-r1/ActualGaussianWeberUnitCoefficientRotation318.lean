module
public import ActualGaussianWeberGaussianScalarCore318
public section

namespace ActualGaussianWeberUnitCoefficientRotation318

open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberQuarterTurnAdd318 ActualGaussianWeberGaussianScalarSpecialization318

variable {K : Type*} [Field K] [DecidableEq K]

/-- A literal positive quarter-turn of the actual Gaussian point scalar
is multiplication of the coefficient by i, for every stock point. -/
theorem quarter_gaussian (h2 : (2 : K) ≠ 0) (i : K) (hi : i^2 = -1)
    (a b : ℤ) (P : WP K) :
    turn h2 i hi (gaussian h2 i hi a b P) = gaussian h2 i hi (-b) a P := by
  let J := turnHom h2 i hi
  have hJ : J (J P) = -P := turn_sq h2 i hi P
  change J (a • P + b • J P) = (-b) • P + a • J P
  simp only [map_add, map_zsmul, hJ, zsmul_neg, neg_zsmul]
  exact add_comm _ _

theorem negative_gaussian (h2 : (2 : K) ≠ 0) (i : K) (hi : i^2 = -1)
    (a b : ℤ) (P : WP K) :
    -(gaussian h2 i hi a b P) = gaussian h2 i hi (-a) (-b) P := by
  let J := turn h2 i hi
  change -(a • P + b • J P) = (-a) • P + (-b) • J P
  simp only [neg_zsmul]
  abel

/-- Remove a fixed -1 turn without altering either of the two compared
points. The resulting coefficient is valid for every later point. -/
theorem undo_negative (h2 : (2 : K) ≠ 0) (i : K) (hi : i^2 = -1)
    (a b : ℤ) (P Q : WP K) (h : gaussian h2 i hi a b P = -Q) :
    gaussian h2 i hi (-a) (-b) P = Q := by
  calc
    _ = -(gaussian h2 i hi a b P) := (negative_gaussian h2 i hi a b P).symm
    _ = -(-Q) := congrArg (fun R : WP K => -R) h
    _ = Q := neg_neg Q

/-- The inverse turn to i is -i, not i. -/
theorem undo_quarter (h2 : (2 : K) ≠ 0) (i : K) (hi : i^2 = -1)
    (a b : ℤ) (P Q : WP K) (h : gaussian h2 i hi a b P = turn h2 i hi Q) :
    gaussian h2 i hi b (-a) P = Q := by
  calc
    _ = -(gaussian h2 i hi (-b) a P) := by
      simpa only [neg_neg] using (negative_gaussian h2 i hi (-b) a P).symm
    _ = -(turn h2 i hi (gaussian h2 i hi a b P)) := by rw [quarter_gaussian]
    _ = -(turn h2 i hi (turn h2 i hi Q)) := congrArg (fun R : WP K => -(turn h2 i hi R)) h
    _ = Q := by rw [turn_sq, neg_neg]

/-- The inverse turn to -i is i. -/
theorem undo_minus_quarter (h2 : (2 : K) ≠ 0) (i : K) (hi : i^2 = -1)
    (a b : ℤ) (P Q : WP K) (h : gaussian h2 i hi a b P = -(turn h2 i hi Q)) :
    gaussian h2 i hi (-b) a P = Q := by
  let J := turnHom h2 i hi
  have hJ : J (J Q) = -Q := turn_sq h2 i hi Q
  calc
    _ = turn h2 i hi (gaussian h2 i hi a b P) := (quarter_gaussian h2 i hi a b P).symm
    _ = J (-(J Q)) := congrArg J h
    _ = Q := by rw [map_neg, hJ, neg_neg]

end ActualGaussianWeberUnitCoefficientRotation318
