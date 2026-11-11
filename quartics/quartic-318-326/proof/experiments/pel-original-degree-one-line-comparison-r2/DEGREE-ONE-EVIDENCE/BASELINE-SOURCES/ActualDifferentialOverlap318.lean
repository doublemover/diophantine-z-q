module
public import ShortInfinityDifferential318
public import WeierstrassOverlap318
public import Mathlib.RingTheory.Kaehler.Basic
public section
noncomputable section
namespace ActualDifferentialOverlap318
open Algebra KaehlerDifferential WeierstrassOverlap318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

@[expose] def actualJacobian (A B : R) : InfinityOverlap A B :=
  algebraMap (Infinity A B) (InfinityOverlap A B) (InfinityChart318.presentation A B).jacobian

theorem actualJacobian_formula (A B : R) :
    actualJacobian A B = ShortInfinityDifferential318.jacobian
      (algebraMap R (InfinityOverlap A B) A) (algebraMap R (InfinityOverlap A B) B)
      (ix A B) (iz A B) := by
  rw [actualJacobian,InfinityChart318.jacobian_formula]
  simp only [map_sub,map_one,map_mul,map_pow,map_ofNat,←IsScalarTower.algebraMap_apply,
    ShortInfinityDifferential318.jacobian,ix,iz]

/-- The literal finite-to-infinity coordinate map gives this actual universal differential identity. -/
theorem invariant_cross_identity (A B : R) :
    actualJacobian A B • D R (InfinityOverlap A B)
      (toInfinityBase A B (ShortAffineJacobian318.x A B)) =
    -(2*toInfinityBase A B (ShortAffineJacobian318.y A B)) •
      D R (InfinityOverlap A B) (ix A B) := by
  rw [actualJacobian_formula,toInfinityBase_x,toInfinityBase_y]
  exact ShortInfinityDifferential318.invariant_cross_identity (D R (InfinityOverlap A B))
    _ _ _ _ _ (Derivation.map_algebraMap _ _) (Derivation.map_algebraMap _ _)
    (WeierstrassOverlap318.infinity_relation A B) (iz_ii A B)

/-- The genuine common open where both differential-chart denominators are invertible. -/
abbrev CommonRing (A B : R) := Localization.Away (actualJacobian A B*(2*ii A B))

@[expose] def commonJacobian (A B : R) : CommonRing A B :=
  algebraMap (InfinityOverlap A B) (CommonRing A B) (actualJacobian A B)
@[expose] def commonFiniteDenominator (A B : R) : CommonRing A B :=
  algebraMap (InfinityOverlap A B) (CommonRing A B) (2*ii A B)
@[expose] def productInverse (A B : R) : CommonRing A B :=
  IsLocalization.Away.invSelf (actualJacobian A B*(2*ii A B))
@[expose] def jacobianInverse (A B : R) : CommonRing A B :=
  commonFiniteDenominator A B*productInverse A B
@[expose] def finiteInverse (A B : R) : CommonRing A B :=
  commonJacobian A B*productInverse A B

theorem common_inverse (A B : R) :
    (commonJacobian A B*commonFiniteDenominator A B)*productInverse A B=1 := by
  rw [commonJacobian,commonFiniteDenominator,←map_mul]
  exact IsLocalization.Away.mul_invSelf _

theorem jacobian_inverse (A B : R) : commonJacobian A B*jacobianInverse A B=1 := by
  unfold jacobianInverse
  rw [←mul_assoc,common_inverse]

theorem finite_inverse (A B : R) : commonFiniteDenominator A B*finiteInverse A B=1 := by
  unfold finiteInverse
  rw [←mul_assoc,mul_comm (commonFiniteDenominator A B),common_inverse]

/-- Both forms are actual elements of the same universal differential module on the actual common open. -/
@[expose] def finiteForm (A B : R) : KaehlerDifferential R (CommonRing A B) :=
  finiteInverse A B • D R (CommonRing A B)
    (algebraMap (InfinityOverlap A B) (CommonRing A B)
      (toInfinityBase A B (ShortAffineJacobian318.x A B)))
@[expose] def infinityForm (A B : R) : KaehlerDifferential R (CommonRing A B) :=
  -jacobianInverse A B • D R (CommonRing A B)
    (algebraMap (InfinityOverlap A B) (CommonRing A B) (ix A B))

/-- The genuine invariant differential overlap has the required negative infinity sign. -/
theorem finiteForm_eq_infinityForm (A B : R) : finiteForm A B=infinityForm A B := by
  let φ := algebraMap (InfinityOverlap A B) (CommonRing A B)
  have h := invariant_cross_identity A B
  have hh := congrArg (KaehlerDifferential.map R R (InfinityOverlap A B) (CommonRing A B)) h
  simp only [map_smul, KaehlerDifferential.map_D,toInfinityBase_y] at hh
  rw [←IsScalarTower.algebraMap_smul (CommonRing A B) (actualJacobian A B),
    ←IsScalarTower.algebraMap_smul (CommonRing A B) (-(2*ii A B)),map_neg] at hh
  have he := congrArg (fun ω : KaehlerDifferential R (CommonRing A B) =>
    (jacobianInverse A B*finiteInverse A B) • ω) hh
  have hj : (jacobianInverse A B*finiteInverse A B)*commonJacobian A B=finiteInverse A B := by
    calc
      _ = finiteInverse A B*(commonJacobian A B*jacobianInverse A B) := by ring
      _ = _ := by rw [jacobian_inverse,mul_one]
  have hf : (jacobianInverse A B*finiteInverse A B)*(-commonFiniteDenominator A B)= -jacobianInverse A B := by
    calc
      _ = -jacobianInverse A B*(commonFiniteDenominator A B*finiteInverse A B) := by ring
      _ = _ := by rw [finite_inverse,mul_one]
  change (jacobianInverse A B*finiteInverse A B) • (commonJacobian A B • _)=
    (jacobianInverse A B*finiteInverse A B) • (-commonFiniteDenominator A B • _) at he
  simpa only [smul_smul,hj,hf,finiteForm,infinityForm] using he

end ActualDifferentialOverlap318
