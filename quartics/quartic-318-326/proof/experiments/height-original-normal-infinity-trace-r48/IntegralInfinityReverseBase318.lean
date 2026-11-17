module
public import IntegralInfinityCommonOrder318
public section
noncomputable section
namespace IntegralInfinityReverseBase318
open Polynomial IntegralSourceBranches318 IntegralInfinityCommonBase318 IntegralInfinityCommonOrder318
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
abbrev InfinityOverlap :=
  Localization.Away (algebraMap R[X] (IntegralInfinityChart318.Base R c) X)
@[expose] def infinityUnit : (InfinityOverlap R c)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := InfinityOverlap R c)
    (algebraMap R[X] (IntegralInfinityChart318.Base R c) X)).unit
@[expose] def finiteUnit : (InfinityOverlap R c)ˣ :=
  Units.map (algebraMap R (InfinityOverlap R c)).toMonoidHom (c 0) * (infinityUnit R c)⁻¹
@[simp] theorem infinityUnit_value : (infinityUnit R c : InfinityOverlap R c) =
    algebraMap (IntegralInfinityChart318.Base R c) (InfinityOverlap R c)
      (algebraMap R[X] (IntegralInfinityChart318.Base R c) X) := IsUnit.unit_spec _

theorem reciprocal_relation :
    (finiteUnit R c : InfinityOverlap R c) * (infinityUnit R c : InfinityOverlap R c) =
      algebraMap R (InfinityOverlap R c) (c 0 : R) := by
  simp only [finiteUnit,Units.val_mul,Units.coe_map]
  change (algebraMap R (InfinityOverlap R c) (c 0 : R) *
    (↑(infinityUnit R c)⁻¹ : InfinityOverlap R c)) * (infinityUnit R c : InfinityOverlap R c) = _
  rw [mul_assoc,Units.inv_mul,mul_one]

@[expose] def rootBaseMap : BranchBase R c 0 →ₐ[R] InfinityOverlap R c :=
  (Polynomial.aeval (finiteUnit R c : InfinityOverlap R c)).comp
    (LinearRootCoordinate318.coordinateEquiv (c 0) (contacts R 0)).toAlgHom

theorem rootBaseMap_root : rootBaseMap R c
    (AdjoinRoot.root (QuadraticPresentation318.polynomial
      (LinearRootCoordinate318.parameter (c 0) (contacts R 0)))) =
      (finiteUnit R c : InfinityOverlap R c) := by
  change Polynomial.aeval (finiteUnit R c : InfinityOverlap R c)
    (LinearRootCoordinate318.forward (c 0) (contacts R 0) _) = _
  rw [LinearRootCoordinate318.forward_root,Polynomial.aeval_X]

theorem other_parameter (j : Fin 3) :
    rootBaseMap R c (algebraMap R[X] (BranchBase R c 0)
      (IntegralBranchChart318.other (otherTwist R c 0) (otherContact R 0) j)) =
    algebraMap R[X] (InfinityOverlap R c) (IntegralInfinityChart318.coefficient R c j) *
      (finiteUnit R c : InfinityOverlap R c)^2 := by
  have hc : otherTwist R c 0 j = c j.succ := by fin_cases j <;> rfl
  have ha : otherContact R 0 j = IntegralInfinityChart318.contact R j := by fin_cases j <;> rfl
  change Polynomial.aeval (finiteUnit R c : InfinityOverlap R c)
    (LinearRootCoordinate318.coordinateEquiv (c 0) (contacts R 0)
      (algebraMap R[X] (BranchBase R c 0)
        (LinearRootCoordinate318.parameter (otherTwist R c 0 j) (otherContact R 0 j)))) = _
  rw [LinearRootCoordinate318.coordinate_other,hc,ha]
  have hC (a : R) : algebraMap R[X] (InfinityOverlap R c) (C a) =
      algebraMap R (InfinityOverlap R c) a :=
    (IsScalarTower.algebraMap_apply R R[X] (InfinityOverlap R c) a).symm
  simp only [map_add,map_mul,map_pow,Polynomial.aeval_C,Polynomial.aeval_X,
    IntegralInfinityChart318.coefficient,map_sub,map_one,map_zero,map_neg,hC,contacts,Matrix.cons_val_zero,zero_sub]
  have h := IntegralReciprocalRootScale318.parameter_identity
    (algebraMap R (InfinityOverlap R c) (c 0 : R))
    (algebraMap R (InfinityOverlap R c) (↑(c 0)⁻¹ : R))
    (finiteUnit R c : InfinityOverlap R c) (infinityUnit R c : InfinityOverlap R c)
    (algebraMap R (InfinityOverlap R c) (IntegralInfinityChart318.contact R j))
    (algebraMap R (InfinityOverlap R c) (c j.succ : R))
    (by rw [←map_mul,Units.mul_inv,map_one]) (reciprocal_relation R c)
  rw [infinityUnit_value,←IsScalarTower.algebraMap_apply] at h
  linear_combination -h

theorem other_parameter_unit (j : Fin 3) :
    IsUnit (rootBaseMap R c (algebraMap R[X] (BranchBase R c 0)
      (IntegralBranchChart318.other (otherTwist R c 0) (otherContact R 0) j))) := by
  rw [other_parameter]
  apply IsUnit.mul _ ((finiteUnit R c).isUnit.pow 2)
  simpa only [←IsScalarTower.algebraMap_apply] using
    (IntegralInfinityChart318.coefficient_unit R c j).map
      (algebraMap (IntegralInfinityChart318.Base R c) (InfinityOverlap R c))

theorem finiteDenominator_unit : IsUnit (rootBaseMap R c
    (IntegralBranchChart318.denominator (c 0) (contacts R 0)
      (otherTwist R c 0) (otherContact R 0))) := by
  simp only [IntegralBranchChart318.denominator,map_prod]
  exact IsUnit.prod_univ_iff.mpr (other_parameter_unit R c)

@[expose] def finiteBaseMap : OpenBase R c 0 →ₐ[R] InfinityOverlap R c where
  __ := IsLocalization.Away.lift (g := (rootBaseMap R c).toRingHom)
    (IntegralBranchChart318.denominator (c 0) (contacts R 0)
      (otherTwist R c 0) (otherContact R 0)) (finiteDenominator_unit R c)
  commutes' r := by
    change IsLocalization.Away.lift (g := (rootBaseMap R c).toRingHom) _ _
      (algebraMap (BranchBase R c 0) (OpenBase R c 0)
        (algebraMap R (BranchBase R c 0) r)) = _
    rw [IsLocalization.Away.lift_eq]
    exact (rootBaseMap R c).commutes r

theorem finiteBaseMap_on_rootBase (a : BranchBase R c 0) :
    finiteBaseMap R c (algebraMap (BranchBase R c 0) (OpenBase R c 0) a) = rootBaseMap R c a := by
  change IsLocalization.Away.lift (g := (rootBaseMap R c).toRingHom)
    (IntegralBranchChart318.denominator (c 0) (contacts R 0)
      (otherTwist R c 0) (otherContact R 0)) (finiteDenominator_unit R c)
    (algebraMap (BranchBase R c 0) (OpenBase R c 0) a) = _
  exact IsLocalization.Away.lift_eq _ (finiteDenominator_unit R c) a

theorem finiteBaseMap_coordinate : finiteBaseMap R c (rootOpen R c) =
    (finiteUnit R c : InfinityOverlap R c) := by
  rw [rootOpen,finiteBaseMap_on_rootBase,rootBaseMap_root]

theorem finiteCoordinate_unit :
    IsUnit ((finiteBaseMap R c).toRingHom (rootOpen R c)) := by
  change IsUnit (finiteBaseMap R c (rootOpen R c))
  rw [finiteBaseMap_coordinate]
  exact (finiteUnit R c).isUnit

/-- The reverse coefficient-base map is constructed from the original
ramified root quotient and its actual localization, without a field argument. -/
@[expose] def finiteOverlapMap : CommonBase R c →ₐ[R] InfinityOverlap R c where
  __ := IsLocalization.Away.lift (g := (finiteBaseMap R c).toRingHom) (rootOpen R c)
    (finiteCoordinate_unit R c)
  commutes' r := by
    change IsLocalization.Away.lift (g := (finiteBaseMap R c).toRingHom)
      (rootOpen R c) (finiteCoordinate_unit R c)
      (algebraMap (OpenBase R c 0) (CommonBase R c) (algebraMap R (OpenBase R c 0) r)) = _
    rw [IsLocalization.Away.lift_eq]
    exact (finiteBaseMap R c).commutes r

theorem finiteOverlapMap_on_base (a : OpenBase R c 0) :
    finiteOverlapMap R c (algebraMap (OpenBase R c 0) (CommonBase R c) a) = finiteBaseMap R c a := by
  change IsLocalization.Away.lift (g := (finiteBaseMap R c).toRingHom)
    (rootOpen R c) (finiteCoordinate_unit R c)
    (algebraMap (OpenBase R c 0) (CommonBase R c) a) = _
  exact IsLocalization.Away.lift_eq _ (finiteCoordinate_unit R c) a

theorem finiteOverlapMap_root : finiteOverlapMap R c (rootUnit R c : CommonBase R c) =
    (finiteUnit R c : InfinityOverlap R c) := by
  rw [rootUnit_value,finiteOverlapMap_on_base,finiteBaseMap_coordinate]

theorem infinityOverlapMap_root : infinityOverlapMap R c (infinityUnit R c : InfinityOverlap R c) =
    (reciprocalUnit R c : CommonBase R c) := by
  rw [infinityUnit_value,infinityOverlapMap_on_base,infinityBaseMap_coordinate]

end IntegralInfinityReverseBase318
