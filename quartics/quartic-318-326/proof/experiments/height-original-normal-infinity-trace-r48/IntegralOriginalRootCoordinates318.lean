module
public import IntegralRationalFiniteAtlas318
public import BranchOriginalCoordinate318
public section
noncomputable section
namespace IntegralOriginalRootCoordinates318
open Polynomial
open scoped TensorProduct
open IntegralSourceBranches318 IntegralBranchCoordinates318 IntegralBranchLocalization318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
@[expose] def root (i : Fin 4) : SourceOrder R c :=
  FourRootOrderSigns318.generator (coefficient R c) i
local instance regroupedCommRing (i : Fin 4) : CommRing (RegroupedOrder R c i) := inferInstance
local instance regroupedAlgebra (i : Fin 4) :
    Algebra (BranchBase R c i) (RegroupedOrder R c i) := inferInstance

theorem regroup_root (i : Fin 4) : sourceRegroup R c i (root R c i) =
    algebraMap (BranchBase R c i) (RegroupedOrder R c i) (rootCoordinate R c i) := by
  rw [rootCoordinate]
  change sourceRegroup R c i (root R c i)=
    algebraMap (BranchBase R c i) (RegroupedOrder R c i)
      (LinearRootCoordinate318.inverse (c i) (contacts R i) X)
  rw [LinearRootCoordinate318.inverse_X]
  fin_cases i
  · exact BranchOriginalCoordinate318.first_root _
  · exact BranchOriginalCoordinate318.second_root _
  · exact BranchOriginalCoordinate318.third_root _
  · exact BranchOriginalCoordinate318.fourth_root _

/-- Every normalized integral branch coordinate is the original ordered root
with its sign, not merely a solution of the same square equation. -/
theorem coordinate_eq_root (i : Fin 4) : sourceCoordinate R c i =
    algebraMap (SourceOrder R c) (B R c i) (root R c i) := by
  apply (sourceLocalizationEquiv R c i).injective
  rw [sourceCoordinate,AlgEquiv.apply_symm_apply,sourceLocalizationEquiv_on_source]
  change openCoordinate R c i =
    localizedSourceEquiv R c i (Algebra.TensorProduct.includeRight (sourceRegroup R c i (root R c i)))
  rw [regroup_root,AlgHom.commutes,
    IsScalarTower.algebraMap_apply (BranchBase R c i) (OpenBase R c i)
      (OpenBase R c i ⊗[BranchBase R c i] RegroupedOrder R c i),AlgEquiv.commutes]
  rfl

theorem rational_root (c : Fin 4 → ℚˣ) (i : Fin 4) :
    IntegralRationalFullOverlap318.sourceEquiv c (root ℚ c i) =
      ContactRootReciprocals318.root c i := rfl
end IntegralOriginalRootCoordinates318
