module
public import OriginalIntegerReciprocalOrderField318
public import FiniteOrderIntegralClosureMap318
public section
noncomputable section
namespace OriginalIntegerReciprocalOrderNormalization318
attribute [local instance] OriginalIntegerReciprocalOrderField318.fieldAlgebra
attribute [local instance] OriginalIntegerReciprocalNormalization318.reciprocalBaseAlgebra
variable (c : Fin 4 → ℚˣ)
abbrev Order := OriginalIntegerReciprocalOrderField318.Order c
abbrev L := OriginalIntegerReciprocalOrderField318.L c
abbrev Closure := OriginalIntegerReciprocalNormalization318.Closure c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField
local instance orderFinite : Module.Finite (Polynomial ℤ) (Order c) :=
  (OriginalIntegerReciprocalCharts318.reciprocal_finite_free c).1

/-- Same original field element, certified integral using the actual monic
reciprocal order and its proved reciprocal polynomial action. -/
@[expose] def toClosure : Order c →ₐ[Polynomial ℤ] Closure c :=
  FiniteOrderIntegralClosureMap318.toClosure
    (OriginalIntegerReciprocalOrderField318.fieldAlgHom c)
    (OriginalIntegerReciprocalOrderField318.fieldEmbedding_injective c)

@[simp] theorem toClosure_val (z : Order c) :
    (toClosure c z).val = OriginalIntegerReciprocalOrderField318.fieldEmbedding c z := rfl

theorem toClosure_injective : Function.Injective (toClosure c) :=
  FiniteOrderIntegralClosureMap318.toClosure_injective
    (OriginalIntegerReciprocalOrderField318.fieldAlgHom c)
    (OriginalIntegerReciprocalOrderField318.fieldEmbedding_injective c)

theorem integral_iff (x : L c) :
    IsIntegral (Order c) x ↔ IsIntegral (Polynomial ℤ) x :=
  FiniteOrderIntegralClosureMap318.integral_iff
    (OriginalIntegerReciprocalOrderField318.fieldAlgHom c) x

/-- The existing reciprocal parameter closure is the integral closure of
THIS reciprocal order inside its proved original fraction field. Finiteness
of the closure/map is deliberately a separate obligation. -/
theorem isIntegralClosure : IsIntegralClosure (Closure c) (Order c) (L c) :=
  FiniteOrderIntegralClosureMap318.isIntegralClosure
    (OriginalIntegerReciprocalOrderField318.fieldAlgHom c)

@[expose] def closureAlgebra : Algebra (Order c) (Closure c) :=
  (toClosure c).toRingHom.toAlgebra

end OriginalIntegerReciprocalOrderNormalization318
