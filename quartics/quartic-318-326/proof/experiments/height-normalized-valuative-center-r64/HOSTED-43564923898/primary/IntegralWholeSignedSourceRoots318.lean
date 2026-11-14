module
public import IntegralWholeGeneratorComparisons318
public import IntegralOtherRootCoordinates318
public section
noncomputable section
namespace IntegralWholeSignedSourceRoots318
open Polynomial IntegralSourceBranches318 IntegralWholeFiniteComparison318
open IntegralWholeReciprocalOrders318 IntegralOriginalRootCoordinates318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

/-- The pivot root becomes the actual finite polynomial coordinate, with its
original sign. This is stronger than the equality of its square with c0*t. -/
theorem comparison_root_zero : comparison R c (root R c 0)=
    algebraMap R[X] (FiniteOrder R c) X := by
  change coordinateComparison R c
    (ThreeRootOrder318.baseChange _ _ (sourceRegroup R c 0 (root R c 0))) = _
  rw [regroup_root,AlgEquiv.commutes]
  change ThreeRootBaseEquivalence318.three _ _ _ _
    (algebraMap (BranchBase R c 0) (RootOrder R c)
      (IntegralBranchCoordinates318.rootCoordinate R c 0)) = _
  rw [ThreeRootBaseEquivalence318.three_base]
  congr 1
  change LinearRootCoordinate318.coordinateEquiv (c 0) (contacts R 0)
    ((LinearRootCoordinate318.coordinateEquiv (c 0) (contacts R 0)).symm X)=X
  exact AlgEquiv.apply_symm_apply _ _

/-- Each of the remaining original signed roots becomes precisely its
corresponding generator in the whole finite order. -/
theorem comparison_root_succ (j : Fin 3) : comparison R c (root R c j.succ)=
    ThreeRootCoordinates318.generator (finiteCoefficient R c) j := by
  change coordinateComparison R c
    (ThreeRootOrder318.baseChange _ _ (sourceRegroup R c 0 (root R c j.succ))) = _
  rw [IntegralOtherRootCoordinates318.regroup_other]
  rw [show ThreeRootOrder318.baseChange _ _
    ((1 : BranchBase R c 0) ⊗ₜ[R[X]]
      ThreeRootCoordinates318.generator
        (IntegralBranchChart318.other (otherTwist R c 0) (otherContact R 0)) j)=
      ThreeRootCoordinates318.generator (rootCoefficient R c) j from
        ThreeRootCoordinates318.coefficientMap_generator _ (BranchBase R c 0) j]
  exact IntegralWholeGeneratorComparisons318.finite_generator R c j

/-- The original common-overlap image of the signed pivot root is the
already constructed invertible root, not an independently chosen square root. -/
theorem source_root_zero :
    IntegralOverlapOpenImmersions318.sourceMap R c (root R c 0)=
      IntegralOverlapChartMaps318.commonMap R c
        (IntegralInfinityCommonBase318.rootUnit R c) := by
  change IntegralOverlapChartMaps318.finiteMap R c
    (algebraMap (SourceOrder R c) (IntegralBranchCoordinates318.B R c 0)
      (root R c 0)) = _
  rw [←coordinate_eq_root,IntegralOverlapChartMaps318.finite_coordinate]
end IntegralWholeSignedSourceRoots318
