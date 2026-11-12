module
public import IntegralElementBaseCutoff318
public import Mathlib.Algebra.Polynomial.Div
public section
noncomputable section
namespace IntegralDenominatorBaseDivisor318
open Polynomial
variable (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]

/-- The cutoff is a literal multiple of the original denominator in
the WHOLE algebra. This strengthens pointwise nonvanishing to the exact
ring divisibility required by localization restriction. -/
theorem exists_divisor (b : A) (hb : b ≠ 0) (hi : IsIntegral R b) :
    ∃ c : R, c ≠ 0 ∧ b ∣ algebraMap R A c := by
  refine ⟨(minpoly R b).coeff 0,IntegralElementBaseCutoff318.constant_ne_zero R A b hi hb,?_⟩
  obtain ⟨P,hP⟩ := Polynomial.X_dvd_sub_C (minpoly R b)
  have h := congrArg (Polynomial.aeval b) hP
  rw [map_sub,map_mul,Polynomial.aeval_X,Polynomial.aeval_C,minpoly.aeval,zero_sub] at h
  refine ⟨-Polynomial.aeval b P,?_⟩
  rw [mul_neg,←h,neg_neg]
end IntegralDenominatorBaseDivisor318
