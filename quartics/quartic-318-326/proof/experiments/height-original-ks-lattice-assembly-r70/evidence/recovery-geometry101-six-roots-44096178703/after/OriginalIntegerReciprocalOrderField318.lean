module
public import OriginalIntegerCommonField318
public import OriginalIntegerReciprocalOrderOverlap318
public import FractionFieldLocalizationDescent318
public section
noncomputable section
namespace OriginalIntegerReciprocalOrderField318
open Polynomial
attribute [local instance] OriginalIntegerCommonField318.fieldAlgebra
attribute [local instance] OriginalIntegerReciprocalOrderOverlap318.commonAlgebra
attribute [local instance] OriginalIntegerReciprocalNormalization318.laurentAlgebra
attribute [local instance] OriginalIntegerReciprocalNormalization318.reciprocalBaseAlgebra
/-- Symbolic-carrier construction avoids expanding the four-root order
while elaborating the inherited RingHom fields. -/
@[expose] def algebraHomOfSquare {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →+* B)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap R B r) : A →ₐ[R] B :=
  { f with commutes' := hf }

private theorem towerOfSquare {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →+* B)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap R B r) :
    @IsScalarTower R A B (inferInstance : Algebra R A).toSMul
      f.toAlgebra.toSMul (inferInstance : Algebra R B).toSMul := by
  letI := f.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (R := R) (S := A) (A := B) (fun r => (hf r).symm)

variable (c : Fin 4 → ℚˣ)
abbrev Order := OriginalIntegerReciprocalOrderOverlap318.Order c
abbrev CommonOrder := OriginalIntegerReciprocalOrderOverlap318.CommonOrder c
abbrev L := OriginalIntegerCommonField318.L c
/-- Capture the already selected native reciprocal-order polynomial action;
this is not a replacement coefficient map. -/
local instance orderPolynomialAlgebra : Algebra ℤ[X] (Order c) := inferInstance
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- The exact reciprocal order is embedded by the existing root-scaled
transition followed by the original common-field map. -/
@[expose] def fieldEmbedding : Order c →+* L c :=
  (OriginalIntegerCommonField318.fieldMap c).comp
    (OriginalIntegerReciprocalOrderOverlap318.infinityMap c)

theorem fieldEmbedding_injective : Function.Injective (fieldEmbedding c) :=
  (OriginalIntegerCommonField318.fieldMap_injective c).comp
    (OriginalIntegerReciprocalOrderOverlap318.infinityMap_injective c)

@[expose] def fieldAlgebra : Algebra (Order c) (L c) := (fieldEmbedding c).toAlgebra
attribute [local instance] fieldAlgebra

/-- The exact s=1/t coefficient map is derived from the actual two restriction
squares, not from equality of finite and reciprocal polynomial actions. -/
theorem fieldEmbedding_on_polynomial (p : ℤ[X]) :
    fieldEmbedding c (algebraMap ℤ[X] (Order c) p) = algebraMap ℤ[X] (L c) p := by
  change OriginalIntegerCommonField318.fieldMap c
    (OriginalIntegerReciprocalOrderOverlap318.infinityMap c
      (algebraMap ℤ[X] (Order c) p)) = _
  rw [OriginalIntegerReciprocalOrderOverlap318.polynomial,
    OriginalIntegerCommonField318.fieldMap_on_laurent]
  rfl

@[expose] def fieldAlgHom : Order c →ₐ[ℤ[X]] L c :=
  algebraHomOfSquare (R := ℤ[X]) (A := Order c) (B := L c) (fieldEmbedding c) (fieldEmbedding_on_polynomial c)

/-- Only the actual reciprocal parameter is a denominator here. Its unit
property follows through the proved localization and this exact field map. -/
theorem parameter_unit : IsUnit (fieldEmbedding c (algebraMap ℤ[X] (Order c) X)) := by
  letI := OriginalIntegerReciprocalOrderOverlap318.localization c
  exact (IsLocalization.Away.algebraMap_isUnit (S := CommonOrder c)
    (algebraMap ℤ[X] (Order c) X)).map (OriginalIntegerCommonField318.fieldMap c)

/-- Explicit named algebra projections for the coefficient/order/field square. -/
theorem field_scalar_tower : @IsScalarTower ℤ[X] (Order c) (L c)
    (inferInstance : Algebra ℤ[X] (Order c)).toSMul (fieldAlgebra c).toSMul
    (OriginalIntegerReciprocalNormalization318.reciprocalBaseAlgebra c).toSMul :=
  towerOfSquare (R := ℤ[X]) (A := Order c) (B := L c) (fieldEmbedding c) (fieldEmbedding_on_polynomial c)

/-- This tower uses the literal composition defining fieldEmbedding. -/
theorem common_field_tower : @IsScalarTower (Order c) (CommonOrder c) (L c)
    (OriginalIntegerReciprocalOrderOverlap318.commonAlgebra c).toSMul
    (OriginalIntegerCommonField318.fieldAlgebra c).toSMul (fieldAlgebra c).toSMul :=
  IsScalarTower.of_algebraMap_eq' (R := Order c) (S := CommonOrder c) (A := L c) rfl

theorem order_domain : IsDomain (Order c) :=
  Function.Injective.isDomain (fieldEmbedding c) (fieldEmbedding_injective c)

/-- Descend the ORIGINAL field identification through the actual reciprocal
parameter localization. No abstract field identification is supplied as a premise. -/
theorem actual_fractionField : IsFractionRing (Order c) (L c) := by
  letI := OriginalIntegerReciprocalOrderOverlap318.localization c
  letI := common_field_tower c
  letI : FaithfulSMul (Order c) (L c) :=
    (faithfulSMul_iff_algebraMap_injective (Order c) (L c)).mpr
      (fieldEmbedding_injective c)
  letI := OriginalIntegerCommonField318.actual_fractionField c
  exact FractionFieldLocalizationDescent318.of_localization (S := CommonOrder c)
    (Submonoid.powers (algebraMap ℤ[X] (Order c) X))

end OriginalIntegerReciprocalOrderField318
