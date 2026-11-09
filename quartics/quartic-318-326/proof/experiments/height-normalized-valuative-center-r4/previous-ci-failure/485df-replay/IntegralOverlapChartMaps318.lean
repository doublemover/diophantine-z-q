module
public import IntegralOverlapCoefficients318
public import IntegralBranchBicanonical318
public import IntegralInfinityCoefficients318
public section
noncomputable section
namespace IntegralOverlapChartMaps318
open Polynomial IntegralSourceBranches318 IntegralInfinityCommonBase318
open IntegralInfinityOverlapRealization318 IntegralBranchLocalization318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
local instance infinityAlgebra :
    Algebra (IntegralInfinityChart318.Base R c) (CommonBase R c) :=
  (infinityBaseMap R c).toRingHom.toAlgebra
local instance infinityTower :
    IsScalarTower R (IntegralInfinityChart318.Base R c) (CommonBase R c) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := IntegralInfinityChart318.Base R c)
    (A := CommonBase R c) (fun r => ((infinityBaseMap R c).commutes r).symm)
abbrev Overlap := CommonBase R c ⊗[OpenBase R c 0] OpenOrder R c 0
local instance overlap_commRing : CommRing (Overlap R c) := inferInstance
local instance overlap_algebra : Algebra R (Overlap R c) := inferInstance
abbrev nativeCotangentModule (A T : Type*) [CommRing A] [CommRing T]
    [Algebra A T] : Module T (KaehlerDifferential A T) := inferInstance

@[expose] def commonMap : CommonBase R c →ₐ[R] Overlap R c :=
  IsScalarTower.toAlgHom R (CommonBase R c) (Overlap R c)
/-- Restriction from the original finite source principal open, through its
proved explicit branch presentation and actual principal overlap inclusion. -/
@[expose] def finiteMap : IntegralBranchCoordinates318.B R c 0 →ₐ[R] Overlap R c :=
  ((Algebra.TensorProduct.includeRight : OpenOrder R c 0 →ₐ[OpenBase R c 0]
    Overlap R c).restrictScalars R).comp (sourceLocalizationEquiv R c 0).toAlgHom
/-- Restriction from the actual infinity order along its principal overlap,
then the inverse of the proved original-root scaling equivalence. -/
@[expose] def infinityMap : IntegralInfinityChart318.Order R c →ₐ[R] Overlap R c :=
  ((actualOverlapEquiv R c).symm.restrictScalars R).toAlgHom.comp
    ((Algebra.TensorProduct.includeRight : IntegralInfinityChart318.Order R c
      →ₐ[IntegralInfinityChart318.Base R c]
        CommonBase R c ⊗[IntegralInfinityChart318.Base R c]
          IntegralInfinityChart318.Order R c).restrictScalars R)

theorem finite_on_base (a : OpenBase R c 0) :
    (Algebra.TensorProduct.includeRight : OpenOrder R c 0 →ₐ[OpenBase R c 0]
      Overlap R c) (algebraMap (OpenBase R c 0) (OpenOrder R c 0) a) =
    commonMap R c (algebraMap (OpenBase R c 0) (CommonBase R c) a) := by
  rw [AlgHom.commutes]
  exact IsScalarTower.algebraMap_apply (OpenBase R c 0) (CommonBase R c) (Overlap R c) a

theorem infinity_on_base (a : IntegralInfinityChart318.Base R c) :
    infinityMap R c (algebraMap (IntegralInfinityChart318.Base R c)
      (IntegralInfinityChart318.Order R c) a) =
    commonMap R c (infinityBaseMap R c a) := by
  change (actualOverlapEquiv R c).symm
    ((Algebra.TensorProduct.includeRight : IntegralInfinityChart318.Order R c
      →ₐ[IntegralInfinityChart318.Base R c] _)
        (algebraMap (IntegralInfinityChart318.Base R c) (IntegralInfinityChart318.Order R c) a)) = _
  rw [AlgHom.commutes,
    IsScalarTower.algebraMap_apply (IntegralInfinityChart318.Base R c) (CommonBase R c)
      (CommonBase R c ⊗[IntegralInfinityChart318.Base R c] IntegralInfinityChart318.Order R c),
    AlgEquiv.commutes]
  rfl

theorem finite_on_polynomial (p : R[X]) :
    finiteMap R c (algebraMap R[X] (IntegralBranchCoordinates318.B R c 0) p) =
      commonMap R c (algebraMap R[X] (CommonBase R c) p) := by
  change Algebra.TensorProduct.includeRight
    (sourceLocalizationEquiv R c 0 (algebraMap R[X] (IntegralBranchCoordinates318.B R c 0) p)) = _
  rw [IsScalarTower.algebraMap_apply R[X] (SourceOrder R c)
    (IntegralBranchCoordinates318.B R c 0),sourceLocalizationEquiv_on_source,
    sourceMap_on_polynomial,finite_on_base,
    ←IsScalarTower.algebraMap_apply R[X] (OpenBase R c 0) (CommonBase R c)]

theorem finite_coordinate :
    finiteMap R c (IntegralBranchCoordinates318.sourceCoordinate R c 0) =
      commonMap R c (rootUnit R c : CommonBase R c) := by
  change Algebra.TensorProduct.includeRight
    (sourceLocalizationEquiv R c 0 ((sourceLocalizationEquiv R c 0).symm
      (IntegralBranchCoordinates318.openCoordinate R c 0))) = _
  rw [AlgEquiv.apply_symm_apply,IntegralBranchCoordinates318.openCoordinate,
    finite_on_base,IntegralBranchCoordinates318.rootCoordinate,LinearRootCoordinate318.inverse_X,
    rootUnit_value]
  rfl

theorem infinity_coordinate :
    infinityMap R c (IntegralInfinityChart318.coordinate R c) =
      commonMap R c (reciprocalUnit R c : CommonBase R c) := by
  rw [IntegralInfinityChart318.coordinate,infinity_on_base,infinityBaseMap_coordinate]

theorem finite_originalT :
    finiteMap R c (IntegralBranchCoordinates318.sourceT R c 0) =
      commonMap R c (IntegralOverlapCoefficients318.originalT R c) := by
  rw [IntegralBranchCoordinates318.sourceT,←IsScalarTower.algebraMap_apply,
    finite_on_polynomial]
  rfl
end IntegralOverlapChartMaps318
