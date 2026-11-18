module
public import OriginalIntegerReciprocalOrderField318
public import OriginalPrimeThreeActualQuotient318
public import FourRootOrderSigns318
public section
noncomputable section
namespace PrimeThreeReciprocalRatios318
open Polynomial
open OriginalIntegerAffineModel318
abbrev twist := OriginalPrimeThreeActualQuotient318.twist
abbrev H := OriginalIntegerReciprocalCharts318.ReciprocalOrder twist
abbrev coeff := IntegralFourRootReciprocalCharts318.reciprocalCoefficient
  (OriginalIntegerReciprocalCharts318.integralTwist twist) contacts
theorem coeff_eq (i : Fin 4) : coeff i = X * (1 - C (contacts i) * X) := by
  norm_num [coeff, IntegralFourRootReciprocalCharts318.reciprocalCoefficient,
    OriginalIntegerReciprocalCharts318.integralTwist, twist, OriginalPrimeThreeActualQuotient318.twist]
variable {F : Type*} [Field F] (g : H →+* F)
@[expose] def scalar : ℤ[X] →+* F := g.comp (algebraMap ℤ[X] H)
@[expose] def z (i : Fin 4) : F := g (FourRootOrderSigns318.generator coeff i)
theorem z_square (i : Fin 4) :
    z g i ^ 2 = scalar g X * (1 - scalar g (C (contacts i)) * scalar g X) := by
  change g (FourRootOrderSigns318.generator coeff i) ^ 2 = _
  rw [← map_pow, FourRootOrderSigns318.generator_square]
  change scalar g (coeff i) = _
  rw [coeff_eq, map_mul, map_sub, map_one, map_mul]

theorem z_zero_square : z g 0 ^ 2 = scalar g X := by
  simpa [contacts] using z_square g 0

/-- The ratio is taken ONLY in the field receiving the actual order;
this does not treat its denominator as an arithmetic chart unit. -/
theorem ratio_square (hs : scalar g X ≠ 0) (i : Fin 3) :
    (z g i.succ / z g 0)^2 = 1 - scalar g (C (contacts i.succ)) * scalar g X := by
  rw [div_pow, z_square, z_zero_square]
  apply (div_eq_iff hs).mpr
  exact mul_comm _ _

theorem restore (hs : scalar g X ≠ 0) (i : Fin 3) :
    z g 0 * (z g i.succ / z g 0) = z g i.succ := by
  have hx : z g 0 ≠ 0 := by
    intro hx
    apply hs
    rw [← z_zero_square g, hx]
    norm_num
  field_simp [hx] <;> ring

abbrev OriginalField := OriginalIntegerReciprocalOrderField318.L twist
local instance originalField : Field OriginalField :=
  (KummerTensorField318.source_raw_field twist).toField
abbrev actualMap : H →+* OriginalField :=
  OriginalIntegerReciprocalOrderField318.fieldEmbedding twist

theorem actual_parameter_nonzero : scalar actualMap X ≠ 0 :=
  (OriginalIntegerReciprocalOrderField318.parameter_unit twist).ne_zero

/-- Both equations refer to the literal root-scaled reciprocal embedding
in the original common function field; s is invertible there only. -/
theorem actual_ratios (i : Fin 3) :
    (z actualMap i.succ / z actualMap 0)^2 =
      1 - scalar actualMap (C (contacts i.succ)) * scalar actualMap X ∧
    z actualMap 0 * (z actualMap i.succ / z actualMap 0) = z actualMap i.succ :=
  ⟨ratio_square actualMap actual_parameter_nonzero i,
   restore actualMap actual_parameter_nonzero i⟩

end PrimeThreeReciprocalRatios318
