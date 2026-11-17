module
public import OriginalIntegerReciprocalRationalNormalization318
public import ContactGlobalProper318
public import SourceOpenFractionField318
public section
noncomputable section
namespace OriginalIntegerReciprocalRationalParameter318
open Polynomial
variable (c : Fin 4 → ℚˣ)
abbrev L := OriginalIntegerFiniteClosure318.L c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField
attribute [local instance] OriginalIntegerReciprocalNormalization318.laurentAlgebra
attribute [local instance] OriginalIntegerReciprocalNormalization318.reciprocalBaseAlgebra
attribute [local instance] OriginalIntegerReciprocalRationalNormalization318.rationalFunctionAlgebra
attribute [local instance] OriginalIntegerReciprocalRationalNormalization318.rationalBaseAlgebra
attribute [local instance] OriginalIntegerAffineModel318.rationalPolynomialAlgebra
attribute [local instance] IntegerPolynomialFractionField318.fieldAlgebra
local instance parameterFraction : IsFractionRing ℤ[X] (RatFunc ℚ) :=
  IntegerPolynomialFractionField318.actual_fractionField

/-- The finite t-coordinate is named with its precise finite action; it is
not the currently selected reciprocal polynomial action. -/
@[expose] def finiteParameter : L c :=
  @algebraMap ℤ[X] (L c) _ _ (OriginalIntegerFiniteClosure318.baseAlgebra c) X

@[expose] def originalReciprocalFieldMap : ℚ[X] →+* L c :=
  (SourceOpenFractionField318.openEmbedding c).comp
    (ContactReciprocalCover318.polynomialMap (ContactKummerOrder318.OpenOrder c))

private theorem mapped_inverse_mul {A F : Type*} [CommRing A] [Field F]
    (g : A →+* F) (u : Aˣ) : g (↑u⁻¹ : A) * g (u : A) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

/-- The reciprocal rational action still sends s to the image of the
original integer reciprocal parameter; extending constants does not alter it. -/
theorem rational_parameter : algebraMap ℚ[X] (L c) X = algebraMap ℤ[X] (L c) X := by
  exact IsFractionRing.lift_algebraMap
    (OriginalIntegerReciprocalFiniteClosure318.coefficient_injective c) (X : ℤ[X])

theorem reciprocal_parameter_mul : algebraMap ℚ[X] (L c) X * finiteParameter c = 1 := by
  rw [rational_parameter]
  change (algebraMap (IntegralWholeReciprocalOverlap318.Laurent ℤ) (L c))
    (IntegralFourRootOverlap318.reciprocalMap ℤ X) * finiteParameter c = 1
  rw [IntegralFourRootOverlap318.reciprocalMap_eval, Polynomial.aeval_X]
  have ht : (algebraMap (IntegralWholeReciprocalOverlap318.Laurent ℤ) (L c))
      (IntegralWholeReciprocalOverlap318.y ℤ : IntegralWholeReciprocalOverlap318.Laurent ℤ) =
      finiteParameter c := by
    rw [IntegralWholeReciprocalOverlap318.y_value]
    exact @IntegralClosureAwayField318.fieldMap_on_base ℤ[X] (L c) _ _
      (OriginalIntegerFiniteClosure318.baseAlgebra c) X
      (OriginalIntegerNormalizedOverlap318.parameterUnit c) X
  rw [← ht]
  exact mapped_inverse_mul _ _

theorem original_parameter_mul : originalReciprocalFieldMap c X * finiteParameter c = 1 := by
  rw [originalReciprocalFieldMap, RingHom.comp_apply,
    ContactReciprocalCover318.polynomial_coordinate]
  let g : ContactKummerOrder318.OpenBase →+* L c :=
    (SourceOpenFractionField318.openEmbedding c).comp
      (algebraMap ContactKummerOrder318.OpenBase (ContactKummerOrder318.OpenOrder c))
  have ht : g (ContactReciprocalBase318.tUnit : ContactKummerOrder318.OpenBase) =
      finiteParameter c := by
    rw [ContactReciprocalBase318.tUnit_coe]
    exact SourceOpenFractionField318.openEmbedding_on_polynomial c X
  change g (↑ContactReciprocalBase318.tUnit⁻¹ : ContactKummerOrder318.OpenBase) *
    finiteParameter c = 1
  rw [← ht]
  exact mapped_inverse_mul g _

/-- The exact reciprocal Q[s] action on L equals the original contact
normalization's reciprocal polynomial map followed by its original embedding.
Only equality of the two s=1/t coordinates and uniqueness on Q are used;
finite and reciprocal polynomial actions are never identified. -/
theorem reciprocal_polynomial_square :
    algebraMap ℚ[X] (L c) = originalReciprocalFieldMap c := by
  apply Polynomial.ringHom_ext
  · intro q
    exact RingHom.congr_fun (Subsingleton.elim
      ((algebraMap ℚ[X] (L c)).comp Polynomial.C)
      ((originalReciprocalFieldMap c).comp Polynomial.C)) q
  · apply mul_right_cancel₀ (show finiteParameter c ≠ 0 from
      OriginalIntegerNormalizedOverlap318.parameter_ne_zero c)
    exact (reciprocal_parameter_mul c).trans (original_parameter_mul c).symm

end OriginalIntegerReciprocalRationalParameter318
