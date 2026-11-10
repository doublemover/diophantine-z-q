module
public import ThreeRootBaseEquivalence318
public section
noncomputable section
namespace IntegralWholeFiniteComparison318
open Polynomial IntegralSourceBranches318 IntegralWholeReciprocalOrders318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
@[expose] def rootCoefficient (j : Fin 3) : BranchBase R c 0 :=
  algebraMap R[X] (BranchBase R c 0)
    (IntegralBranchChart318.other (otherTwist R c 0) (otherContact R 0) j)
abbrev RootOrder := ThreeRootOrder318.Order (rootCoefficient R c)

/-- The WHOLE original four-root order, not a branch localization, is first
regrouped and base-changed over its actual first root algebra. -/
@[expose] def firstComparison : SourceOrder R c ≃ₐ[R[X]] RootOrder R c :=
  (sourceRegroup R c 0).trans
    ((ThreeRootOrder318.baseChange
      (IntegralBranchChart318.other (otherTwist R c 0) (otherContact R 0))
      (BranchBase R c 0)).restrictScalars R[X])

@[expose] def coordinateEquiv : BranchBase R c 0 ≃ₐ[R] R[X] :=
  LinearRootCoordinate318.coordinateEquiv (c 0) (contacts R 0)

theorem coefficient_comparison (j : Fin 3) :
    coordinateEquiv R c (rootCoefficient R c j)=finiteCoefficient R c j := by
  have hd : otherTwist R c 0 j=c j.succ := by fin_cases j <;> rfl
  have ha : otherContact R 0 j=IntegralInfinityChart318.contact R j := by fin_cases j <;> rfl
  change LinearRootCoordinate318.coordinateEquiv (c 0) (contacts R 0)
    (algebraMap R[X] (BranchBase R c 0)
      (LinearRootCoordinate318.parameter (otherTwist R c 0 j) (otherContact R 0 j))) = _
  rw [LinearRootCoordinate318.coordinate_other,hd,ha]
  simp only [contacts,Matrix.cons_val_zero,zero_sub,map_neg,map_mul,finiteCoefficient]
  ring

/-- Coefficient-preserving integral equivalence with the full finite
polynomial-coordinate order. Every original root factor is retained. -/
@[expose] def coordinateComparison : RootOrder R c ≃ₐ[R] FiniteOrder R c :=
  { ThreeRootBaseEquivalence318.three (coordinateEquiv R c).toRingEquiv
      (rootCoefficient R c) (finiteCoefficient R c) (coefficient_comparison R c) with
    commutes' := by
      intro r
      rw [IsScalarTower.algebraMap_apply R (BranchBase R c 0) (RootOrder R c),
        ThreeRootBaseEquivalence318.three_base,AlgEquiv.commutes]
      exact (IsScalarTower.algebraMap_apply R R[X] (FiniteOrder R c) r).symm }

@[expose] def comparison : SourceOrder R c ≃ₐ[R] FiniteOrder R c :=
  ((firstComparison R c).restrictScalars R).trans (coordinateComparison R c)

/-- Literal original t coordinate, with its original twist; this prevents
using an unnamed isomorphism of finite algebras in the projective join. -/
theorem comparison_t : comparison R c (algebraMap R[X] (SourceOrder R c) X)=
    algebraMap R[X] (FiniteOrder R c) (C (↑(c 0)⁻¹:R)*X^2) := by
  change coordinateComparison R c (firstComparison R c
    (algebraMap R[X] (SourceOrder R c) X)) = _
  rw [AlgEquiv.commutes,IsScalarTower.algebraMap_apply R[X] (BranchBase R c 0) (RootOrder R c)]
  change ThreeRootBaseEquivalence318.three _ _ _ _
    (algebraMap (BranchBase R c 0) (RootOrder R c)
      (algebraMap R[X] (BranchBase R c 0) X)) = _
  rw [ThreeRootBaseEquivalence318.three_base]
  congr 1
  have h := LinearRootCoordinate318.coordinate_contact (c 0) (contacts R 0)
  simpa only [contacts,Matrix.cons_val_zero,map_zero,sub_zero] using h
end IntegralWholeFiniteComparison318
