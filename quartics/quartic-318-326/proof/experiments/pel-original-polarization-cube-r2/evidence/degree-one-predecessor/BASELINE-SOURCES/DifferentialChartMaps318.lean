module
public import ActualDifferentialOverlap318
public section
noncomputable section
namespace DifferentialChartMaps318
open Algebra KaehlerDifferential WeierstrassOverlap318 ActualDifferentialOverlap318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]
abbrev FiniteChart (A B : R) := Localization.Away (ShortAffineJacobian318.presentation A B 1).jacobian
abbrev InfinityChart (A B : R) := InfinityChart318.SmoothRing A B

@[expose] def finiteBaseMap (A B : R) : Affine A B →ₐ[R] CommonRing A B :=
  (Algebra.algHom R (InfinityOverlap A B) (CommonRing A B)).comp (toInfinityBase A B)
@[expose] def infinityBaseMap (A B : R) : Infinity A B →ₐ[R] CommonRing A B :=
  Algebra.algHom R (Infinity A B) (CommonRing A B)

theorem finiteBaseMap_jacobian (A B : R) :
    finiteBaseMap A B (ShortAffineJacobian318.presentation A B 1).jacobian=commonFiniteDenominator A B := by
  rw [ShortAffineJacobian318.jacobian_y]
  simp only [finiteBaseMap, AlgHom.comp_apply, map_mul, map_ofNat, toInfinityBase_y]
  simp only [commonFiniteDenominator, Algebra.algHom_apply, map_mul, map_ofNat]
  rfl

theorem infinityBaseMap_jacobian (A B : R) :
    infinityBaseMap A B (InfinityChart318.presentation A B).jacobian=commonJacobian A B := by
  exact (IsScalarTower.algebraMap_apply (Infinity A B) (InfinityOverlap A B) (CommonRing A B) _).symm

/-- Actual algebra maps from both genuine Jacobian charts to the common open. -/
@[expose] def finiteChartMap (A B : R) : FiniteChart A B →ₐ[R] CommonRing A B :=
  IsLocalization.Away.liftAlgHom (f := finiteBaseMap A B)
    (ShortAffineJacobian318.presentation A B 1).jacobian (by
      rw [finiteBaseMap_jacobian]
      exact IsUnit.of_mul_eq_one_right (finiteInverse A B) (by rw [mul_comm,finite_inverse]))
@[expose] def infinityChartMap (A B : R) : InfinityChart A B →ₐ[R] CommonRing A B :=
  IsLocalization.Away.liftAlgHom (f := infinityBaseMap A B)
    (InfinityChart318.presentation A B).jacobian (by
      rw [infinityBaseMap_jacobian]
      exact IsUnit.of_mul_eq_one_right (jacobianInverse A B) (by rw [mul_comm,jacobian_inverse]))

@[simp] theorem finiteChartMap_integral (A B : R) (s : Affine A B) :
    finiteChartMap A B (algebraMap (Affine A B) (FiniteChart A B) s)=finiteBaseMap A B s := by
  simp [finiteChartMap,IsLocalization.Away.liftAlgHom_apply]
@[simp] theorem infinityChartMap_integral (A B : R) (s : Infinity A B) :
    infinityChartMap A B (algebraMap (Infinity A B) (InfinityChart A B) s)=infinityBaseMap A B s := by
  simp [infinityChartMap,IsLocalization.Away.liftAlgHom_apply]

theorem finiteChartMap_inverse (A B : R) :
    finiteChartMap A B (IsLocalization.Away.invSelf (ShortAffineJacobian318.presentation A B 1).jacobian)=finiteInverse A B := by
  have h := congrArg (finiteChartMap A B) (IsLocalization.Away.mul_invSelf
    (S := FiniteChart A B) (ShortAffineJacobian318.presentation A B 1).jacobian)
  simp only [map_mul,map_one,finiteChartMap_integral,finiteBaseMap_jacobian] at h
  calc
    _ = (finiteInverse A B*commonFiniteDenominator A B)*
        finiteChartMap A B (IsLocalization.Away.invSelf (ShortAffineJacobian318.presentation A B 1).jacobian) := by
          rw [mul_comm (finiteInverse A B),finite_inverse,one_mul]
    _ = finiteInverse A B*(commonFiniteDenominator A B*
        finiteChartMap A B (IsLocalization.Away.invSelf (ShortAffineJacobian318.presentation A B 1).jacobian)) := by ring
    _ = _ := by rw [h,mul_one]

theorem infinityChartMap_inverse (A B : R) :
    infinityChartMap A B (IsLocalization.Away.invSelf (InfinityChart318.presentation A B).jacobian)=jacobianInverse A B := by
  have h := congrArg (infinityChartMap A B) (IsLocalization.Away.mul_invSelf
    (S := InfinityChart A B) (InfinityChart318.presentation A B).jacobian)
  simp only [map_mul,map_one,infinityChartMap_integral,infinityBaseMap_jacobian] at h
  calc
    _ = (jacobianInverse A B*commonJacobian A B)*
        infinityChartMap A B (IsLocalization.Away.invSelf (InfinityChart318.presentation A B).jacobian) := by
          rw [mul_comm (jacobianInverse A B),jacobian_inverse,one_mul]
    _ = jacobianInverse A B*(commonJacobian A B*
        infinityChartMap A B (IsLocalization.Away.invSelf (InfinityChart318.presentation A B).jacobian)) := by ring
    _ = _ := by rw [h,mul_one]

end DifferentialChartMaps318
