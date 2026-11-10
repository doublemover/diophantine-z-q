module
public import LocalizedTensorRestriction318
public section
noncomputable section
namespace IntegralOriginalCommonRestriction318
open Polynomial IntegralWholeReciprocalOrders318 IntegralWholeReciprocalOverlap318
open IntegralWholeFiniteComparison318 IntegralWholeOrderOpenMaps318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
abbrev OldOverlap := IntegralOverlapChartMaps318.Overlap R c

/-- Restriction of the actual full finite order to the OLD overlap is the
original source restriction conjugated by the explicit signed-root comparison. -/
@[expose] def finiteRestriction : FiniteOrder R c →ₐ[R] OldOverlap R c :=
  (IntegralOverlapOpenImmersions318.sourceMap R c).comp (comparison R c).symm.toAlgHom
@[expose] def oldY : (OldOverlap R c)ˣ :=
  Units.map (IntegralOverlapChartMaps318.commonMap R c).toMonoidHom
    (IntegralInfinityCommonBase318.rootUnit R c)

theorem finiteRestriction_X :
    finiteRestriction R c (algebraMap R[X] (FiniteOrder R c) X)=(oldY R c:OldOverlap R c) := by
  rw [←IntegralWholeSignedSourceRoots318.comparison_root_zero]
  change IntegralOverlapOpenImmersions318.sourceMap R c
    ((comparison R c).symm (comparison R c _)) = _
  rw [AlgEquiv.symm_apply_apply,IntegralWholeSignedSourceRoots318.source_root_zero]
  rfl

theorem finiteRestriction_generator (j : Fin 3) :
    finiteRestriction R c (ThreeRootCoordinates318.generator (finiteCoefficient R c) j)=
      (1 ⊗ₜ[IntegralSourceBranches318.OpenBase R c 0]
        IntegralOverlapRootGenerators318.finiteGenerator R c j : OldOverlap R c) := by
  rw [←IntegralWholeSignedSourceRoots318.comparison_root_succ]
  change IntegralOverlapOpenImmersions318.sourceMap R c
    ((comparison R c).symm (comparison R c _)) = _
  rw [AlgEquiv.symm_apply_apply,IntegralOtherRootCoordinates318.common_other]

theorem finiteRestriction_unit :
    IsUnit (finiteRestriction R c (algebraMap R[X] (FiniteOrder R c) X)) := by
  rw [finiteRestriction_X]
  exact (oldY R c).isUnit

/-- The old overlap maps into the full punctured order by the genuine
localization universal property, without discarding any whole-order points. -/
@[expose] def commonRestriction : CommonOrder R c →+* OldOverlap R c :=
  (LocalizedTensorRestriction318.lift (L:=Laurent R) X
    (finiteRestriction R c).toRingHom (finiteRestriction_unit R c)).comp
      (finiteBaseChange R c).symm.toRingHom

theorem common_finite (a : FiniteOrder R c) :
    commonRestriction R c (finiteMap R c a)=finiteRestriction R c a := by
  change LocalizedTensorRestriction318.lift _ _ _
    ((finiteBaseChange R c).symm (finiteBaseChange R c (1 ⊗ₜ[R[X]] a))) = _
  rw [AlgEquiv.symm_apply_apply,LocalizedTensorRestriction318.lift_right]

theorem common_y :
    commonRestriction R c (IntegralWholeOrderScalarMaps318.commonY R c)=oldY R c := by
  change commonRestriction R c
    (algebraMap (Laurent R) (CommonOrder R c) (y R:Laurent R)) = _
  rw [y_value,←IntegralWholeOrderScalarMaps318.finite_polynomial,common_finite,
    finiteRestriction_X]

theorem common_constant (r : R) :
    commonRestriction R c (algebraMap R (CommonOrder R c) r)=
      algebraMap R (OldOverlap R c) r := by
  change commonRestriction R c (algebraMap (Laurent R) (CommonOrder R c)
    (algebraMap R[X] (Laurent R) (C r))) = _
  rw [←IntegralWholeOrderScalarMaps318.finite_polynomial,common_finite]
  exact (finiteRestriction R c).commutes r

@[expose] def commonAlgRestriction : CommonOrder R c →ₐ[R] OldOverlap R c where
  __ := commonRestriction R c
  commutes' := common_constant R c
end IntegralOriginalCommonRestriction318
