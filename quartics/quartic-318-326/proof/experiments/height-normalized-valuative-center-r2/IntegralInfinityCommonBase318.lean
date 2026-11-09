module
public import IntegralBranchLocalization318
public import IntegralInfinityChart318
public import IntegralReciprocalRootScale318
public section
noncomputable section
namespace IntegralInfinityCommonBase318
open Polynomial IntegralSourceBranches318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
@[expose] def rootOpen : OpenBase R c 0 :=
  algebraMap (BranchBase R c 0) (OpenBase R c 0)
    (AdjoinRoot.root (QuadraticPresentation318.polynomial
      (LinearRootCoordinate318.parameter (c 0) (contacts R 0))))
abbrev CommonBase := Localization.Away (rootOpen R c)
@[expose] def rootUnit : (CommonBase R c)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := CommonBase R c) (rootOpen R c)).unit
@[expose] def reciprocalUnit : (CommonBase R c)ˣ :=
  Units.map (algebraMap R (CommonBase R c)).toMonoidHom (c 0) * (rootUnit R c)⁻¹

@[simp] theorem rootUnit_value : (rootUnit R c : CommonBase R c) =
    algebraMap (OpenBase R c 0) (CommonBase R c) (rootOpen R c) :=
  IsUnit.unit_spec _

theorem reciprocal_relation :
    (rootUnit R c : CommonBase R c) * (reciprocalUnit R c : CommonBase R c) =
      algebraMap R (CommonBase R c) (c 0 : R) := by
  simp only [reciprocalUnit,Units.val_mul,Units.coe_map]
  change (rootUnit R c : CommonBase R c) *
    (algebraMap R (CommonBase R c) (c 0 : R) * (↑(rootUnit R c)⁻¹ : CommonBase R c)) = _
  calc
    _ = algebraMap R (CommonBase R c) (c 0 : R) *
      ((rootUnit R c : CommonBase R c) * (↑(rootUnit R c)⁻¹ : CommonBase R c)) := by ring
    _ = _ := by rw [Units.mul_inv,mul_one]

/-- The original affine t really is the square of the original ramified root
with its original inverse twist on this actual localization. -/
theorem polynomial_X : algebraMap R[X] (CommonBase R c) X =
    algebraMap R (CommonBase R c) (↑(c 0)⁻¹ : R) * (rootUnit R c : CommonBase R c)^2 := by
  have h := congrArg (algebraMap (BranchBase R c 0) (CommonBase R c))
    (LinearRootCoordinate318.contact_square (c 0) (contacts R 0))
  have hroot : algebraMap (BranchBase R c 0) (CommonBase R c)
      (AdjoinRoot.root (QuadraticPresentation318.polynomial
        (LinearRootCoordinate318.parameter (c 0) (contacts R 0)))) =
        (rootUnit R c : CommonBase R c) := by
    exact (IsScalarTower.algebraMap_apply (BranchBase R c 0) (OpenBase R c 0)
      (CommonBase R c) _).trans (rootUnit_value R c).symm
  simp only [map_mul,map_pow] at h
  rw [←IsScalarTower.algebraMap_apply R[X] (BranchBase R c 0) (CommonBase R c),
    ←IsScalarTower.algebraMap_apply R (BranchBase R c 0) (CommonBase R c),hroot] at h
  simpa only [contacts,Matrix.cons_val_zero,Polynomial.C_0,sub_zero] using h

@[expose] def reciprocalPolynomial : R[X] →ₐ[R] CommonBase R c :=
  Polynomial.aeval (reciprocalUnit R c : CommonBase R c)
@[expose] def finiteParameter (j : Fin 3) : CommonBase R c :=
  algebraMap (OpenBase R c 0) (CommonBase R c)
    (algebraMap R[X] (OpenBase R c 0)
      (IntegralBranchChart318.other (otherTwist R c 0) (otherContact R 0) j))
@[expose] def infinityParameter (j : Fin 3) : CommonBase R c :=
  reciprocalPolynomial R c (IntegralInfinityChart318.coefficient R c j)

theorem finiteParameter_shape (j : Fin 3) : finiteParameter R c j =
    algebraMap R (CommonBase R c) (c j.succ : R) *
      (algebraMap R (CommonBase R c) (↑(c 0)⁻¹ : R) * (rootUnit R c : CommonBase R c)^2 -
        algebraMap R (CommonBase R c) (IntegralInfinityChart318.contact R j)) := by
  have hc : otherTwist R c 0 j = c j.succ := by fin_cases j <;> rfl
  have ha : otherContact R 0 j = IntegralInfinityChart318.contact R j := by fin_cases j <;> rfl
  simp only [finiteParameter,IntegralBranchChart318.other,LinearRootCoordinate318.parameter,
    hc,ha,←IsScalarTower.algebraMap_apply,map_mul,map_sub]
  rw [polynomial_X]
  rfl

theorem infinityParameter_shape (j : Fin 3) : infinityParameter R c j =
    algebraMap R (CommonBase R c) (c j.succ : R) *
      algebraMap R (CommonBase R c) (↑(c 0)⁻¹ : R) *
      (1-algebraMap R (CommonBase R c) (IntegralInfinityChart318.contact R j) *
        algebraMap R (CommonBase R c) (↑(c 0)⁻¹ : R) * (reciprocalUnit R c : CommonBase R c)^2) := by
  simp only [infinityParameter,reciprocalPolynomial,IntegralInfinityChart318.coefficient,
    map_mul,map_sub,map_one,map_pow,Polynomial.aeval_C,Polynomial.aeval_X]

theorem parameter_identity (j : Fin 3) : finiteParameter R c j =
    infinityParameter R c j * (rootUnit R c : CommonBase R c)^2 := by
  rw [finiteParameter_shape,infinityParameter_shape]
  have h := IntegralReciprocalRootScale318.parameter_identity
    (algebraMap R (CommonBase R c) (c 0 : R))
    (algebraMap R (CommonBase R c) (↑(c 0)⁻¹ : R))
    (rootUnit R c : CommonBase R c) (reciprocalUnit R c : CommonBase R c)
    (algebraMap R (CommonBase R c) (IntegralInfinityChart318.contact R j))
    (algebraMap R (CommonBase R c) (c j.succ : R))
    (by rw [←map_mul,Units.mul_inv,map_one]) (reciprocal_relation R c)
  exact h.symm.trans (mul_comm _ _)

theorem infinityParameter_unit (j : Fin 3) : IsUnit (infinityParameter R c j) := by
  have h := (IntegralBranchChart318.other_unit (c 0) (contacts R 0)
    (otherTwist R c 0) (otherContact R 0) j).map
      (algebraMap (OpenBase R c 0) (CommonBase R c))
  change IsUnit (finiteParameter R c j) at h
  rw [parameter_identity] at h
  exact isUnit_of_mul_isUnit_left h

theorem infinityDenominator_unit :
    IsUnit (reciprocalPolynomial R c (IntegralInfinityChart318.denominator R c)) := by
  simp only [IntegralInfinityChart318.denominator,map_prod]
  exact IsUnit.prod_univ_iff.mpr (infinityParameter_unit R c)

/-- The actual finite overlap maps to the infinity coordinate base because
its original other-root factors, not arbitrary replacements, are units. -/
@[expose] def infinityBaseMap : IntegralInfinityChart318.Base R c →ₐ[R] CommonBase R c where
  __ := IsLocalization.Away.lift (g := (reciprocalPolynomial R c).toRingHom)
    (IntegralInfinityChart318.denominator R c) (infinityDenominator_unit R c)
  commutes' r := by
    change IsLocalization.Away.lift (g := (reciprocalPolynomial R c).toRingHom)
      (IntegralInfinityChart318.denominator R c) (infinityDenominator_unit R c)
      (algebraMap R[X] (IntegralInfinityChart318.Base R c) (C r)) = _
    rw [IsLocalization.Away.lift_eq]
    exact Polynomial.aeval_C _ _

theorem infinityBaseMap_polynomial (p : R[X]) :
    infinityBaseMap R c (algebraMap R[X] (IntegralInfinityChart318.Base R c) p) =
      reciprocalPolynomial R c p :=
  IsLocalization.Away.lift_eq (g := (reciprocalPolynomial R c).toRingHom)
    (IntegralInfinityChart318.denominator R c) (infinityDenominator_unit R c) p

theorem infinityBaseMap_coordinate :
    infinityBaseMap R c (algebraMap R[X] (IntegralInfinityChart318.Base R c) X) =
      (reciprocalUnit R c : CommonBase R c) := by
  rw [infinityBaseMap_polynomial]
  exact Polynomial.aeval_X _

end IntegralInfinityCommonBase318
