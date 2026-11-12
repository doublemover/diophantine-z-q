module
public import DifferentialChartMaps318
public import AlgHomDifferential318
public section
noncomputable section
namespace InvariantChartForms318
open KaehlerDifferential WeierstrassOverlap318 ActualDifferentialOverlap318 DifferentialChartMaps318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

/-- Actual finite-chart invariant form, not a fraction in an unrelated field. -/
@[expose] def finite (A B : R) : KaehlerDifferential R (FiniteChart A B) :=
  IsLocalization.Away.invSelf (S := FiniteChart A B) (ShortAffineJacobian318.presentation A B 1).jacobian •
    D R (FiniteChart A B) (algebraMap (Affine A B) (FiniteChart A B) (ShortAffineJacobian318.x A B))
/-- Actual infinity-chart invariant form, with the negative sign. -/
@[expose] def infinity (A B : R) : KaehlerDifferential R (InfinityChart A B) :=
  -IsLocalization.Away.invSelf (S := InfinityChart A B) (InfinityChart318.presentation A B).jacobian •
    D R (InfinityChart A B) (algebraMap (Infinity A B) (InfinityChart A B) (InfinityChart318.x A B))

theorem finite_pullback (A B : R) :
    AlgHomDifferential318.map (finiteChartMap A B) (finite A B)=finiteForm A B := by
  rw [finite,AlgHomDifferential318.map_smul,AlgHomDifferential318.map_D,
    finiteChartMap_inverse,finiteChartMap_integral]
  rfl

theorem infinity_pullback (A B : R) :
    AlgHomDifferential318.map (infinityChartMap A B) (infinity A B)=infinityForm A B := by
  rw [infinity,AlgHomDifferential318.map_smul,AlgHomDifferential318.map_D,
    map_neg,infinityChartMap_inverse,infinityChartMap_integral]
  unfold infinityForm
  congr 2

/-- The pullbacks of the two actual invariant forms agree in the actual universal
    differential module of their common Jacobian open, over every commutative base ring. -/
theorem invariant_overlap (A B : R) :
    AlgHomDifferential318.map (finiteChartMap A B) (finite A B)=
      AlgHomDifferential318.map (infinityChartMap A B) (infinity A B) := by
  rw [finite_pullback,infinity_pullback,finiteForm_eq_infinityForm]
end InvariantChartForms318
