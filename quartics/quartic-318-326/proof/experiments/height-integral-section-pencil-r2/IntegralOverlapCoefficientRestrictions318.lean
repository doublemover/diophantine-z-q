module
public import IntegralOverlapChartMaps318
public section
noncomputable section
namespace IntegralOverlapCoefficientRestrictions318
open Polynomial IntegralSourceBranches318 IntegralInfinityCommonBase318
open IntegralOverlapCoefficients318 IntegralOverlapChartMaps318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

theorem finite_denominator :
    finiteMap R c (algebraMap (SourceOrder R c) (IntegralBranchCoordinates318.B R c 0)
      (IntegralBranchDenominatorCover318.denominator R c 0)) =
      commonMap R c (finiteDenominator R c) := by
  rw [IntegralBranchDenominatorCover318.denominator,
    ←IsScalarTower.algebraMap_apply,finite_on_polynomial]
  congr 1
  have hc (j : Fin 3) : coefficient R c (FourRootPivot318.indices 0 j.succ) =
      IntegralBranchChart318.other (otherTwist R c 0) (otherContact R 0) j := rfl
  simp only [IntegralBranchDenominatorCover318.twisted,map_prod,hc,
    finiteDenominator,finiteParameter,←IsScalarTower.algebraMap_apply]

/-- Equality of inverse elements uses their two actual product identities,
not an unrecorded choice of a fraction-field inverse. -/
theorem inverse_unique {A : Type*} [CommRing A] (a b d : A)
    (hb : a*b=1) (hd : a*d=1) : b=d := by
  apply (isUnit_iff_exists_inv.mpr ⟨b,hb⟩).mul_left_cancel.mp
  exact hb.trans hd.symm

theorem finite_inverse_restriction :
    finiteMap R c (IsLocalization.Away.invSelf
      (IntegralBranchDenominatorCover318.denominator R c 0)) =
      commonMap R c (finiteInverse R c) := by
  have hf := congrArg (finiteMap R c) (IsLocalization.Away.mul_invSelf
    (IntegralBranchDenominatorCover318.denominator R c 0))
  rw [map_mul,map_one,finite_denominator] at hf
  have hc := congrArg (commonMap R c) (finite_inverse R c)
  rw [map_mul,map_one] at hc
  exact inverse_unique _ _ _ hf hc

theorem twist0_value : (IntegralBranchDenominatorCover318.twistUnit R c 0 : R) =
    ∏ j : Fin 3, (c j.succ : R) := by
  simp only [IntegralBranchDenominatorCover318.twistUnit,map_prod,Fin.prod_univ_succ,
    FourRootPivot318.indices]
  rfl

/-- The common-base formula is precisely the restriction of the original
finite chart coefficient, including every twist and denominator. -/
theorem finite_coefficient0 :
    finiteMap R c (IntegralBranchBicanonical318.coefficient0 R c 0) =
      commonMap R c (finite0 R c) := by
  simp only [IntegralBranchBicanonical318.coefficient0,map_mul,map_ofNat,
    AlgHom.commutes,finite_inverse_restriction,twist0_value,finite0,twists,k]
  simp only [map_mul,map_ofNat,AlgHom.commutes]

theorem finite_coefficient1 :
    finiteMap R c (IntegralBranchBicanonical318.coefficient1 R c 0) =
      commonMap R c (finite1 R c) := by
  rw [IntegralBranchBicanonical318.coefficient1,map_mul,
    finite_originalT,finite_coefficient0,finite1,map_mul]

theorem infinity_inverse_restriction :
    infinityMap R c (IntegralInfinityChart318.inverseDenominator R c) =
      commonMap R c (infinityInverse R c) := by
  rw [IntegralInfinityChart318.inverseDenominator,infinity_on_base]
  rfl

/-- The infinity coefficients are restricted through the actual scaled-root
order equivalence, not merely compared in a common generic field. -/
theorem infinity_coefficient0 :
    infinityMap R c (IntegralInfinityCoefficients318.coefficient0 R c) =
      commonMap R c (infinity0 R c) := by
  simp only [IntegralInfinityCoefficients318.coefficient0,
    IntegralInfinityCoefficients318.otherTwists,IntegralInfinityCoefficients318.k0,
    map_mul,map_pow,map_ofNat,AlgHom.commutes,infinity_coordinate,
    infinity_inverse_restriction,infinity0,twists,k]
  simp only [map_mul,map_pow,map_ofNat,AlgHom.commutes]

theorem infinity_coefficient1 :
    infinityMap R c (IntegralInfinityCoefficients318.coefficient1 R c) =
      commonMap R c (infinity1 R c) := by
  simp only [IntegralInfinityCoefficients318.coefficient1,
    IntegralInfinityCoefficients318.otherTwists,IntegralInfinityCoefficients318.k0,
    map_mul,map_pow,map_ofNat,AlgHom.commutes,infinity_inverse_restriction,
    infinity1,twists,k]
  simp only [map_mul,map_pow,map_ofNat,AlgHom.commutes]
end IntegralOverlapCoefficientRestrictions318
