module
public import ComplexSphereFourPointNormalization318
public section
noncomputable section
namespace ComplexSphereInfinityQuadruple318
open ComplexSphereFourPointNormalization318
open scoped OnePoint

/-- Compute the chosen normalization using its actual finite-coordinate
choice specification, rather than assuming that choice reduces by rfl. -/
lemma finite_coordinate (a b c:ℂ)
    (h:Function.Injective (![∞,(a:ℂ),(b:ℂ),(c:ℂ)]:Fin 4→OnePoint ℂ)) (j:Fin 3) :
    finiteCoordinate ![∞,(a:ℂ),(b:ℂ),(c:ℂ)] h j=(![a,b,c]:Fin 3→ℂ) j := by
  apply OnePoint.coe_injective
  rw [finiteCoordinate_spec]
  fin_cases j <;> rfl

lemma parameter_eq (a b c:ℂ)
    (h:Function.Injective (![∞,(a:ℂ),(b:ℂ),(c:ℂ)]:Fin 4→OnePoint ℂ)) :
    parameter ![∞,(a:ℂ),(b:ℂ),(c:ℂ)] h=(c-a)/(b-a) := by
  simp only [parameter,finite_coordinate]
end ComplexSphereInfinityQuadruple318
