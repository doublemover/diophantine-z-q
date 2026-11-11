module
public import InvariantFormFrames318
public import FiniteInvariantDifferential318
public import AffineDifferentialSheaf318
public section
noncomputable section
namespace InvariantNormalizedFrames318
open KaehlerDifferential
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
section Generic
variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]

/-- Normalize a genuine rank-one module frame at a proved unit-valued section. -/
@[expose] def normalize (e : M ≃ₗ[S] S) (ω : M) (h : IsUnit (e ω)) : M ≃ₗ[S] S :=
  e.trans (LinearEquiv.smulOfUnit (M:=S) h.unit⁻¹)

theorem normalize_value (e : M ≃ₗ[S] S) (ω : M) (h : IsUnit (e ω)) :
    normalize e ω h ω=1 := by
  change (↑h.unit⁻¹ : S) * e ω=1
  calc
    _ = (↑h.unit⁻¹ : S) * ↑h.unit := congrArg (fun a : S => (↑h.unit⁻¹ : S)*a) h.unit_spec.symm
    _ = 1 := Units.inv_mul h.unit

theorem normalize_inverse_one (e : M ≃ₗ[S] S) (ω : M) (h : IsUnit (e ω)) :
    (normalize e ω h).symm 1=ω := by
  apply (normalize e ω h).injective
  rw [LinearEquiv.apply_symm_apply,normalize_value]
end Generic

variable {R : Type*} [CommRing R]

theorem finite_value_unit (A B : R) :
    IsUnit (WeierstrassKaehler318.affineFrame A B 1 (InvariantChartForms318.finite A B)) := by
  rw [InvariantFormFrames318.finite_frame_value]
  exact IsUnit.of_mul_eq_one_right
    (algebraMap (WeierstrassOverlap318.Affine A B) (DifferentialChartMaps318.FiniteChart A B)
      (ShortAffineJacobian318.presentation A B 1).jacobian)
    (IsLocalization.Away.mul_invSelf _)

theorem x_value_unit (A B : R) :
    IsUnit (WeierstrassKaehler318.affineFrame A B 0 (FiniteInvariantDifferential318.xForm A B)) := by
  rw [FiniteInvariantDifferential318.x_frame_value]
  apply IsUnit.neg
  exact IsUnit.of_mul_eq_one_right
    (algebraMap (WeierstrassOverlap318.Affine A B) (FiniteInvariantDifferential318.XChart A B)
      (ShortAffineJacobian318.presentation A B 0).jacobian)
    (IsLocalization.Away.mul_invSelf _)

theorem infinity_value_unit (A B : R) :
    IsUnit (WeierstrassKaehler318.infinityFrame A B (InvariantChartForms318.infinity A B)) := by
  rw [InvariantFormFrames318.infinity_frame_value]
  apply IsUnit.neg
  exact IsUnit.of_mul_eq_one_right
    (algebraMap (WeierstrassOverlap318.Infinity A B) (DifferentialChartMaps318.InfinityChart A B)
      (InfinityChart318.presentation A B).jacobian)
    (IsLocalization.Away.mul_invSelf _)

@[expose] def finiteFrame (A B : R) := normalize (WeierstrassKaehler318.affineFrame A B 1)
  (InvariantChartForms318.finite A B) (finite_value_unit A B)
@[expose] def xFrame (A B : R) := normalize (WeierstrassKaehler318.affineFrame A B 0)
  (FiniteInvariantDifferential318.xForm A B) (x_value_unit A B)
@[expose] def infinityFrame (A B : R) := normalize (WeierstrassKaehler318.infinityFrame A B)
  (InvariantChartForms318.infinity A B) (infinity_value_unit A B)

theorem finite_normalized (A B : R) : finiteFrame A B (InvariantChartForms318.finite A B)=1 :=
  normalize_value _ _ _
theorem x_normalized (A B : R) : xFrame A B (FiniteInvariantDifferential318.xForm A B)=1 :=
  normalize_value _ _ _
theorem infinity_normalized (A B : R) : infinityFrame A B (InvariantChartForms318.infinity A B)=1 :=
  normalize_value _ _ _
end InvariantNormalizedFrames318
