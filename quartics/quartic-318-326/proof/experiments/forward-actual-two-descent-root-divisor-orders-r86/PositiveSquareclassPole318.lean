module
public import TwoTorsionTwistRealization318
public section
noncomputable section
namespace PositiveSquareclassPole318
open NormalizedPolePoints318 TwoTwistPointRealization318

/-- A rational parametrization chosen uniformly for every positive prescribed
squareclass. No square root of the prescribed coefficient is introduced. -/
def denominator (C : ℚ) : ℚ := 17*(C+1)^2+C
def factor (C : ℚ) : ℚ := 34*(C+1)/denominator C
def complement (C : ℚ) : ℚ := (17*(C+1)^2-C)/denominator C
def pole (C : ℚ) : ℚ := C*(factor C)^2

theorem denominator_pos (C : ℚ) (hC : 0<C) : 0<denominator C := by
  unfold denominator
  positivity

theorem factor_pos (C : ℚ) (hC : 0<C) : 0<factor C := by
  unfold factor
  exact div_pos (by positivity) (denominator_pos C hC)

theorem complement_pos (C : ℚ) (hC : 0<C) : 0<complement C := by
  unfold complement
  apply div_pos _ (denominator_pos C hC)
  nlinarith [sq_nonneg C]

/-- The two exact squareclasses hold simultaneously: pole=C*z^2 and its
complement is a rational square. This is an algebraic conic identity. -/
theorem complement_identity (C : ℚ) (hC : 0<C) :
    1-pole C/17=(complement C)^2 := by
  unfold pole factor complement
  field_simp [ne_of_gt (denominator_pos C hC)]
  unfold denominator
  ring

theorem pole_bounds (C : ℚ) (hC : 0<C) : 0<pole C ∧ pole C<17 := by
  have hz := factor_pos C hC
  have hr := complement_pos C hC
  have he := complement_identity C hC
  constructor
  · unfold pole
    exact mul_pos hC (sq_pos_of_ne_zero (ne_of_gt hz))
  · have hs : 0<(complement C)^2 := sq_pos_of_ne_zero (ne_of_gt hr)
    nlinarith

/-- An actual simultaneous-twist realization at a positive pole with any
prescribed positive squareclass C. The particular source-assignment factor
is not claimed equal to this constructed factor. -/
def realization (C : ℚ) (hC : 0<C) : Realization (pole C) :=
  TwoTorsionTwistRealization318.ofSquareComplement (pole C) (complement C)
    (ne_of_gt (pole_bounds C hC).1) (ne_of_gt (complement_pos C hC))
    (complement_identity C hC)

def certificate (C : ℚ) (hC : 0<C) : Certificate (pole C) :=
  (realization C hC).certificate (ne_of_gt (pole_bounds C hC).1)

/-- Prescribed positive squareclasses alone never obstruct the elementary
pole construction. This does not assert compatibility with a fixed CRT orbit. -/
theorem exists_certified_pole (C : ℚ) (hC : 0<C) :
    ∃ b z : ℚ, 0<b ∧ b<17 ∧ z≠0 ∧ b=C*z^2 ∧ Nonempty (Certificate b) := by
  exact ⟨pole C,factor C,(pole_bounds C hC).1,(pole_bounds C hC).2,
    ne_of_gt (factor_pos C hC),rfl,⟨certificate C hC⟩⟩

end PositiveSquareclassPole318
