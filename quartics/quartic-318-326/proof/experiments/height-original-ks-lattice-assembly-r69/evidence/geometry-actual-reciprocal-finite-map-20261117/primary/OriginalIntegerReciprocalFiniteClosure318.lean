module
public import OriginalIntegerReciprocalOrderField318
public import FiniteOrderFractionExtension318
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public section
noncomputable section
namespace OriginalIntegerReciprocalFiniteClosure318
open Polynomial
attribute [local instance] OriginalIntegerReciprocalOrderField318.fieldAlgebra
attribute [local instance] OriginalIntegerReciprocalNormalization318.reciprocalBaseAlgebra
variable (c : Fin 4 → ℚˣ)
abbrev R := Polynomial ℤ
abbrev K := FractionRing R
abbrev Order := OriginalIntegerReciprocalOrderField318.Order c
abbrev L := OriginalIntegerReciprocalOrderField318.L c
abbrev Closure := OriginalIntegerReciprocalNormalization318.Closure c
local instance sourceField : Field (L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- Injectivity of the actual reciprocal coefficient action follows from
the rank-sixteen free order and its same-field embedding. -/
theorem coefficient_injective : Function.Injective (algebraMap R (L c)) := by
  letI : Module.Free R (Order c) :=
    (OriginalIntegerReciprocalCharts318.reciprocal_finite_free c).2
  letI : Nontrivial (Order c) := Module.nontrivial_of_finrank_pos (R := R)
    (by rw [OriginalIntegerReciprocalCharts318.reciprocal_rank]; decide)
  intro a b h
  apply FaithfulSMul.algebraMap_injective R (Order c)
  apply OriginalIntegerReciprocalOrderField318.fieldEmbedding_injective c
  simpa only [OriginalIntegerReciprocalOrderField318.fieldEmbedding_on_polynomial] using h

/-- Extend precisely the reciprocal coefficient action to its fraction
field. This does not identify that action with the finite-chart action. -/
@[expose] def coefficientFieldAlgebra : Algebra K (L c) :=
  (IsFractionRing.lift (coefficient_injective c) : K →+* L c).toAlgebra
attribute [local instance] coefficientFieldAlgebra

local instance coefficientTower : @IsScalarTower R K (L c)
    (inferInstance : Algebra R K).toSMul (coefficientFieldAlgebra c).toSMul
    (OriginalIntegerReciprocalNormalization318.reciprocalBaseAlgebra c).toSMul :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := K) (A := L c)
    (fun p => (IsFractionRing.lift_algebraMap (coefficient_injective c) p).symm)

/-- The finite extension is derived from the actual monic reciprocal
order and the proved original fraction field, not an added premise. -/
theorem extension_finite : Module.Finite K (L c) := by
  letI := OriginalIntegerReciprocalOrderField318.order_domain c
  letI := OriginalIntegerReciprocalOrderField318.field_scalar_tower c
  letI := OriginalIntegerReciprocalOrderField318.actual_fractionField c
  letI : Module.Finite R (Order c) :=
    (OriginalIntegerReciprocalCharts318.reciprocal_finite_free c).1
  exact FiniteOrderFractionExtension318.finite R (Order c) K (L c)
    (coefficient_injective c)

/-- The trace-lattice theorem applies over normal Noetherian Z[s], not
by falsely calling this two-dimensional parameter ring Dedekind. -/
theorem closure_finite : Module.Finite R (Closure c) := by
  letI := extension_finite c
  exact IsIntegralClosure.finite R K (L c) (Closure c)

theorem closure_noetherian : IsNoetherianRing (Closure c) := by
  letI := extension_finite c
  exact IsIntegralClosure.isNoetherianRing R K (L c) (Closure c)

end OriginalIntegerReciprocalFiniteClosure318
