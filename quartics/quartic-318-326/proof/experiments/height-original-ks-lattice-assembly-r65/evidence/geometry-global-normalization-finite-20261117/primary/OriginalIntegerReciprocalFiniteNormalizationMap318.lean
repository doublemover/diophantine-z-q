module
public import OriginalIntegerReciprocalOrderNormalization318
public import OriginalIntegerReciprocalFiniteClosure318
public import Mathlib.RingTheory.Finiteness.Basic
public section
noncomputable section
namespace OriginalIntegerReciprocalFiniteNormalizationMap318
attribute [local instance] OriginalIntegerReciprocalNormalization318.reciprocalBaseAlgebra
attribute [local instance] OriginalIntegerReciprocalOrderNormalization318.closureAlgebra
variable (c : Fin 4 → ℚˣ)
abbrev R := Polynomial ℤ
abbrev Order := OriginalIntegerReciprocalOrderNormalization318.Order c
abbrev Closure := OriginalIntegerReciprocalOrderNormalization318.Closure c

/-- The coefficient/order/closure square is the commutation law of the
actual same-element algebra map. It is not a new compatibility premise. -/
theorem coefficient_tower : @IsScalarTower R (Order c) (Closure c)
    (inferInstance : Algebra R (Order c)).toSMul
    (OriginalIntegerReciprocalOrderNormalization318.closureAlgebra c).toSMul
    (inferInstance : Algebra R (Closure c)).toSMul :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := Order c) (A := Closure c)
    (fun r => ((OriginalIntegerReciprocalOrderNormalization318.toClosure c).commutes r).symm)

/-- A finite coefficient spanning set also spans over the embedded order.
Only the proof-local R-action on the middle carrier is selected explicitly,
to match the proved algebra-projection tower. The actual order-to-closure
algebra, and hence the resulting finite morphism, are unchanged. -/
theorem finite : Module.Finite (Order c) (Closure c) := by
  letI : SMul R (Order c) := (inferInstance : Algebra R (Order c)).toSMul
  letI := coefficient_tower c
  letI := OriginalIntegerReciprocalFiniteClosure318.closure_finite c
  exact Module.Finite.of_restrictScalars_finite R (Order c) (Closure c)

end OriginalIntegerReciprocalFiniteNormalizationMap318
