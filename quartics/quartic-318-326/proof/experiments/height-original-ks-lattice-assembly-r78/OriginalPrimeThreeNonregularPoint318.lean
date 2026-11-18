module
public import OriginalPrimeThreeLocalizedCotangent318
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.RegularLocalRing.Defs
public section
noncomputable section
namespace OriginalPrimeThreeNonregularPoint318
open Polynomial
open OriginalPrimeThreeFirstOrderPoint318
open OriginalPrimeThreeCotangentIndependence318
open OriginalPrimeThreeLocalizedCotangent318

attribute [local instance] OriginalIntegerFiniteClosure318.baseAlgebra
local instance sourceField :
    Field (OriginalIntegerFractionField318.L OriginalPrimeThreeActualQuotient318.twist) :=
  (KummerTensorField318.source_raw_field OriginalPrimeThreeActualQuotient318.twist).toField

/-- Integral incomparability bounds the dimension of the actual closure
by that of its original integer polynomial base. No claim about generic
dimension is substituted for an arithmetic dimension bound. -/
theorem closure_dimension_le_base : ringKrullDim Closure ≤ ringKrullDim ℤ[X] := by
  letI : Algebra.IsIntegral ℤ[X] Closure := inferInstance
  apply Order.krullDim_le_of_strictMono
    (PrimeSpectrum.comap (algebraMap ℤ[X] Closure))
  intro p q hpq
  exact Ideal.IsIntegral.under_lt_under (R := ℤ[X]) hpq

theorem integer_polynomial_dimension_le_two : ringKrullDim ℤ[X] ≤ 2 := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing]
  have h : ringKrullDim ℤ ≤ 1 :=
    (Ring.krullDimLE_iff (n := 1) (R := ℤ)).mp inferInstance
  calc
    ringKrullDim ℤ + 1 ≤ 1 + 1 := add_le_add_right h 1
    _ = 2 := by norm_num

/-- This is a bound on the literal local ring at the constructed maximal
ideal of the actual normalization, not merely on its special fiber. -/
theorem pointRing_dimension_le_two : ringKrullDim PointRing ≤ 2 := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height pointIdeal PointRing]
  have hne : pointIdeal ≠ ⊤ := (inferInstance : pointIdeal.IsMaximal).ne_top
  exact (Ideal.height_le_ringKrullDim_of_ne_top hne).trans
    (closure_dimension_le_base.trans integer_polynomial_dimension_le_two)

/-- The normalization alone is NOT an arithmetic regular model at this
explicit prime-three point. The proof compares the actual local cotangent
dimension (at least three) with its actual local Krull dimension (at most
two). It does not claim anything about a subsequent resolution. -/
theorem actual_normalized_point_not_regular : ¬ IsRegularLocalRing PointRing := by
  intro hreg
  have he := (IsRegularLocalRing.iff_finrank_cotangentSpace PointRing).mp hreg
  have h3 : (3 : WithBot ℕ∞) ≤ ringKrullDim PointRing := by
    rw [← he]
    exact_mod_cast local_cotangent_finrank_ge_three
  have h32 : (3 : WithBot ℕ∞) ≤ 2 := h3.trans pointRing_dimension_le_two
  norm_num at h32

end OriginalPrimeThreeNonregularPoint318
