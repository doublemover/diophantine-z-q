module
public import IntegerPolynomialLocalization318
public import SourceFractionField318
public import FractionFieldLocalizationDescent318
public section
noncomputable section
namespace OriginalIntegerFractionField318
open Polynomial
open scoped TensorProduct
open OriginalIntegerAffineModel318
attribute [local instance] OriginalIntegerAffineModel318.rationalPolynomialAlgebra
variable (c : Fin 4 → ℚˣ)

abbrev RationalOrder := ContactKummerOrder318.SourceOrder c
abbrev L := SourceFractionField318.L c

local instance fieldInstance : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- This is the previously constructed root-scaled embedding, not an
unspecified algebra structure on the rational order. -/
@[expose] def rationalOrderAlgebra : Algebra (Order c) (RationalOrder c) :=
  (embedding c).toAlgebra
attribute [local instance] rationalOrderAlgebra

/-- Base change with the original integral order as scalar ring, retaining
its precise inclusion into the original rational four-root source. -/
@[expose] def localizedEquiv :
    Order c ⊗[ℤ[X]] ℚ[X] ≃ₐ[Order c] RationalOrder c :=
  { (Algebra.TensorProduct.comm ℤ[X] (Order c) ℚ[X]).toRingEquiv.trans
      (rationalFiber c).toRingEquiv with
    commutes' := by intro x; rfl }

/-- The rational affine source is obtained by inverting only coefficient
denominators inside the actual integer order. -/
theorem rational_order_localization :
    IsLocalization
      (Algebra.algebraMapSubmonoid (Order c) IntegerPolynomialLocalization318.denominators)
      (RationalOrder c) := by
  letI : IsLocalization IntegerPolynomialLocalization318.denominators ℚ[X] :=
    IntegerPolynomialLocalization318.rational_polynomial_localization
  with_reducible_and_instances
    exact IsLocalization.isLocalization_of_algEquiv
      (S := Order c ⊗[ℤ[X]] ℚ[X]) (P := RationalOrder c) _ (localizedEquiv c)

@[expose] def rationalFieldAlgebra : Algebra (RationalOrder c) (L c) :=
  (ContactKummerOrder318.embedding c).toAlgebra
attribute [local instance] rationalFieldAlgebra

/-- The integral model maps into the same original Kummer field by the
composition of the two previously proved injective embeddings. -/
@[expose] def fieldEmbedding : Order c →+* L c :=
  (ContactKummerOrder318.embedding c).comp (embedding c)

@[expose] def integerFieldAlgebra : Algebra (Order c) (L c) :=
  (fieldEmbedding c).toAlgebra
attribute [local instance] integerFieldAlgebra

theorem fieldEmbedding_injective : Function.Injective (fieldEmbedding c) :=
  (ContactKummerOrder318.embedding_injective c).comp (embedding_injective c)

/-- Exact compatibility of the named embeddings; no scalar compatibility
or fraction-field identification is supplied as a hypothesis. -/
theorem field_scalar_tower : IsScalarTower (Order c) (RationalOrder c) (L c) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The original Kummer field is the actual fraction field of the cleared
integer order. This proves neither normality nor regularity of that order. -/
theorem actual_fractionField : IsFractionRing (Order c) (L c) := by
  letI : IsScalarTower (Order c) (RationalOrder c) (L c) := field_scalar_tower c
  letI : FaithfulSMul (Order c) (L c) :=
    (faithfulSMul_iff_algebraMap_injective (Order c) (L c)).mpr (fieldEmbedding_injective c)
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (Order c) IntegerPolynomialLocalization318.denominators)
      (RationalOrder c) := rational_order_localization c
  letI : IsFractionRing (RationalOrder c) (L c) := SourceFractionField318.actual_fractionField c
  exact FractionFieldLocalizationDescent318.of_localization
    (S := RationalOrder c)
    (Algebra.algebraMapSubmonoid (Order c) IntegerPolynomialLocalization318.denominators)

end OriginalIntegerFractionField318
