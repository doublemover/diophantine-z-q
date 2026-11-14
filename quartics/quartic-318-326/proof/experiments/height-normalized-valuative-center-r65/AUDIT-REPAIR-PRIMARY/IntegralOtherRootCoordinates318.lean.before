module
public import IntegralOriginalRootCoordinates318
public import IntegralOverlapRootGenerators318
public section
noncomputable section
namespace IntegralOtherRootCoordinates318
open Polynomial
open IntegralSourceBranches318 IntegralBranchLocalization318 IntegralOriginalRootCoordinates318
open IntegralOverlapRootGenerators318 IntegralOverlapChartMaps318 IntegralOverlapOpenImmersions318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
local instance regroupedCommRing : CommRing (RegroupedOrder R c 0) := inferInstance
local instance regroupedAlgebra : Algebra (BranchBase R c 0) (RegroupedOrder R c 0) := inferInstance

/-- At the pivot-zero chart, the other three original roots keep their
original order under the actual four-to-three tensor reassociation. -/
theorem regroup_other (j : Fin 3) :
    sourceRegroup R c 0 (root R c j.succ) =
      (1 : BranchBase R c 0) ⊗ₜ[R[X]]
        ThreeRootCoordinates318.generator
          (IntegralBranchChart318.other (otherTwist R c 0) (otherContact R 0)) j := by
  fin_cases j <;>
    simp [sourceRegroup,FourRootPivot318.regroup,FourRootPivot318.pivot,
      ThreeRootOrder318.fourRootRegroup,root,FourRootOrderSigns318.generator,
      ThreeRootCoordinates318.generator,Algebra.TensorProduct.one_def,
      AlgEquiv.trans_apply,AlgEquiv.refl_apply,Algebra.TensorProduct.assoc_tmul]

/-- Every finite generator is literally the image of its signed original
source root, through the already used source restriction. -/
theorem sourceMap_other (j : Fin 3) :
    IntegralBranchLocalization318.sourceMap R c 0 (root R c j.succ) =
      finiteGenerator R c j := by
  change localizedSourceEquiv R c 0
    (1 ⊗ₜ[BranchBase R c 0] sourceRegroup R c 0 (root R c j.succ)) = _
  rw [regroup_other]
  unfold localizedSourceEquiv IntegralBranchChart318.localizedOrderEquiv
  rw [AlgEquiv.trans_apply,Algebra.TensorProduct.cancelBaseChange_tmul,one_smul]
  exact ThreeRootCoordinates318.coefficientMap_generator _ (OpenBase R c 0) j

/-- The common tensor restriction of each finite root equals the original
whole-source map, including all three labeled signs. -/
theorem common_other (j : Fin 3) :
    (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j : Overlap R c) =
      IntegralOverlapOpenImmersions318.sourceMap R c (root R c j.succ) := by
  change _ = Algebra.TensorProduct.includeRight
    (sourceLocalizationEquiv R c 0
      (algebraMap (SourceOrder R c) (IntegralBranchCoordinates318.B R c 0)
        (root R c j.succ)))
  rw [sourceLocalizationEquiv_on_source,sourceMap_other]
  rfl
end IntegralOtherRootCoordinates318
