module
public import PELPrimeNormalizerRelations318
public import InertiaLabels318
public section
noncomputable section
namespace PELInertiaNormalizerData318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELQuaternionDivision318
set_option maxHeartbeats 1200000
/-- Exact original five inertia divisors, in their original index order. -/
@[expose] def discriminant : Fin 5 → ℕ := ![30,42,70,105,210]
/-- Signs are fixed so the split-real lower-left entries are positive. -/
@[expose] def coefficients : Fin 5 → Coordinates :=
  ![![-6,4,12,-5],![0,1,0,-1],![-14,5,28,-5],![-21,9,42,-10],![0,1,0,0]]
@[expose] def element (i : Fin 5) : B := embed (coefficients i)

theorem label_identity (i : Fin 5) :
    InertiaLabels318.divisor (InertiaLabels318.fiveLabels i)=discriminant i :=
  InertiaLabels318.five_literal_divisors i

theorem discriminant_positive (i : Fin 5) : 0<(discriminant i:ℚ) := by
  fin_cases i <;> norm_num [discriminant]

theorem element_mem (i : Fin 5) : element i∈order := ⟨coefficients i,rfl⟩
theorem element_trace (i : Fin 5) : reducedTrace (element i)=0 := by
  fin_cases i <;> norm_num [element,coefficients,embed,reducedTrace]
theorem element_norm (i : Fin 5) : reducedNorm (element i)=discriminant i := by
  fin_cases i <;> norm_num [element,coefficients,embed,reducedNorm,discriminant]
theorem element_square (i : Fin 5) :
    element i*element i=algebraMap ℚ B (-(discriminant i:ℚ)) := by
  fin_cases i <;> ext <;>
    norm_num [element,coefficients,embed,discriminant,QuaternionAlgebra.algebraMap_eq]
theorem element_imI_ne_zero (i : Fin 5) : (element i).imI≠0 := by
  fin_cases i <;> norm_num [element,coefficients,embed]
theorem element_ne_zero (i : Fin 5) : element i≠0 := by
  intro h
  exact element_imI_ne_zero i (by rw [h]; rfl)
@[expose] def rationalUnit (i : Fin 5) : Bˣ :=
  ⟨element i,reciprocal (element i),mul_reciprocal _ (element_ne_zero i),
    reciprocal_mul _ (element_ne_zero i)⟩
/-- The projective involution relation retains its exact negative scalar. -/
theorem unit_square (i : Fin 5) :
    (rationalUnit i:B)*(rationalUnit i:B)=algebraMap ℚ B (-(discriminant i:ℚ)) :=
  element_square i
end PELInertiaNormalizerData318
