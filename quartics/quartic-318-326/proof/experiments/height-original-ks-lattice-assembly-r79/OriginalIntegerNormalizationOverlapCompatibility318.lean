module
public import OriginalIntegerReciprocalOrderNormalization318
public import OriginalIntegerNormalizedOverlap318
public section
noncomputable section
namespace OriginalIntegerNormalizationOverlapCompatibility318
attribute [local instance] OriginalIntegerReciprocalNormalization318.laurentAlgebra
variable (c : Fin 4 → ℚˣ)
abbrev Laurent := OriginalIntegerCommonField318.Laurent
abbrev CommonOrder := OriginalIntegerCommonField318.CommonOrder c
abbrev L := OriginalIntegerCommonField318.L c
abbrev Overlap := OriginalIntegerNormalizedOverlap318.Overlap c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField
local instance commonFinite : Module.Finite Laurent (CommonOrder c) :=
  (FourRootOrder318.finite_free _).1

/-- The common order's exact same-field embedding respects the already
fixed Laurent action, by the proved coefficient square. -/
@[expose] def commonAlgHom : CommonOrder c →ₐ[Laurent] L c :=
  { OriginalIntegerCommonField318.fieldMap c with
    commutes' := OriginalIntegerCommonField318.fieldMap_on_laurent c }

/-- The common monic order maps into the literal normalized overlap.
Its finite Laurent-module structure supplies integrality, not a new premise. -/
@[expose] def toOverlap : CommonOrder c →ₐ[Laurent] Overlap c :=
  FiniteOrderIntegralClosureMap318.toClosure (commonAlgHom c)
    (OriginalIntegerCommonField318.fieldMap_injective c)

@[simp] theorem toOverlap_val (z : CommonOrder c) :
    (toOverlap c z).val = OriginalIntegerCommonField318.fieldMap c z := rfl

theorem toOverlap_injective : Function.Injective (toOverlap c) :=
  FiniteOrderIntegralClosureMap318.toClosure_injective (commonAlgHom c)
    (OriginalIntegerCommonField318.fieldMap_injective c)

/-- The finite-chart normalization restriction is the actual common map. -/
theorem finite_square (z : OriginalIntegerAffineModel318.Order c) :
    toOverlap c (OriginalIntegerCommonField318.finiteMap c z) =
      OriginalIntegerNormalizedOverlap318.orderToOverlap c z := by
  apply Subtype.ext
  change OriginalIntegerCommonField318.fieldMap c
    (OriginalIntegerCommonField318.finiteMap c z) =
      OriginalIntegerFractionField318.fieldEmbedding c z
  exact OriginalIntegerCommonField318.fieldMap_on_finite c z

/-- The reciprocal-chart normalization restriction is the SAME common map.
Only literal field elements are compared; finite and reciprocal polynomial
actions are not identified. -/
theorem infinity_square (z : OriginalIntegerReciprocalOrderNormalization318.Order c) :
    toOverlap c (OriginalIntegerReciprocalOrderOverlap318.infinityMap c z) =
      OriginalIntegerReciprocalNormalization318.inclusion c
        (OriginalIntegerReciprocalOrderNormalization318.toClosure c z) := by
  apply Subtype.ext
  change OriginalIntegerCommonField318.fieldMap c
    (OriginalIntegerReciprocalOrderOverlap318.infinityMap c z) =
      OriginalIntegerReciprocalOrderField318.fieldEmbedding c z
  rfl

end OriginalIntegerNormalizationOverlapCompatibility318
