module
public import IntegralInfinityOverlapRealization318
public import IntegralReciprocalTensorIdentity318
public section
noncomputable section
namespace IntegralOverlapCoefficients318
open Polynomial IntegralSourceBranches318 IntegralInfinityCommonBase318
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
@[expose] def finiteDenominator : CommonBase R c := ∏ j : Fin 3, finiteParameter R c j
@[expose] def infinityDenominator : CommonBase R c := ∏ j : Fin 3, infinityParameter R c j
@[expose] def finiteInverse : CommonBase R c :=
  algebraMap (OpenBase R c 0) (CommonBase R c)
    (IsLocalization.Away.invSelf
      (IntegralBranchChart318.denominator (c 0) (contacts R 0)
        (otherTwist R c 0) (otherContact R 0)))
@[expose] def infinityInverse : CommonBase R c :=
  infinityBaseMap R c (IsLocalization.Away.invSelf (IntegralInfinityChart318.denominator R c))
@[expose] def k : CommonBase R c := algebraMap R (CommonBase R c) (↑(c 0)⁻¹ : R)
@[expose] def twists : CommonBase R c :=
  algebraMap R (CommonBase R c) (∏ j : Fin 3, (c j.succ : R))
@[expose] def finite0 : CommonBase R c := 4*twists R c*k R c*finiteInverse R c
@[expose] def infinity0 : CommonBase R c :=
  4*twists R c*k R c^5*(reciprocalUnit R c : CommonBase R c)^2*infinityInverse R c
@[expose] def infinity1 : CommonBase R c :=
  4*twists R c*k R c^4*infinityInverse R c
@[expose] def originalT : CommonBase R c := algebraMap R[X] (CommonBase R c) X
@[expose] def finite1 : CommonBase R c := originalT R c*finite0 R c
@[expose] def derivativeFactor : CommonBase R c :=
  -((rootUnit R c : CommonBase R c)*(↑(reciprocalUnit R c)⁻¹ : CommonBase R c))

theorem finite_inverse : finiteDenominator R c*finiteInverse R c=1 := by
  have h := congrArg (algebraMap (OpenBase R c 0) (CommonBase R c))
    (IsLocalization.Away.mul_invSelf
      (IntegralBranchChart318.denominator (c 0) (contacts R 0)
        (otherTwist R c 0) (otherContact R 0)))
  simpa only [finiteDenominator,finiteParameter,finiteInverse,
    IntegralBranchChart318.denominator,map_prod,map_mul,map_one,
    ←IsScalarTower.algebraMap_apply] using h

theorem infinity_inverse : infinityDenominator R c*infinityInverse R c=1 := by
  have h := congrArg (infinityBaseMap R c)
    (IsLocalization.Away.mul_invSelf (IntegralInfinityChart318.denominator R c))
  simpa only [map_mul,map_one,infinityBaseMap_polynomial,
    IntegralInfinityChart318.denominator,map_prod,infinityDenominator,
    infinityParameter,infinityInverse] using h

theorem denominator_transition : finiteDenominator R c =
    infinityDenominator R c*(rootUnit R c : CommonBase R c)^6 := by
  simp only [finiteDenominator,infinityDenominator,parameter_identity,
    Fin.prod_univ_succ]
  ring

/-- Exact squared Jacobian transport in the actual integral coefficient
localization. This also holds in residue characteristic two. -/
theorem coefficient0_transition :
    finite0 R c*derivativeFactor R c^2=infinity0 R c := by
  exact IntegralReciprocalTensorIdentity318.coefficient_transport
    (algebraMap R (CommonBase R c) (c 0 : R)) (k R c)
    (rootUnit R c : CommonBase R c) (reciprocalUnit R c : CommonBase R c)
    (↑(reciprocalUnit R c)⁻¹ : CommonBase R c) (twists R c)
    (finiteDenominator R c) (finiteInverse R c)
    (infinityDenominator R c) (infinityInverse R c)
    (by rw [k,←map_mul,Units.mul_inv,map_one]) (reciprocal_relation R c)
    (Units.mul_inv _) (finite_inverse R c) (infinity_inverse R c)
    (denominator_transition R c)

theorem reciprocal_square_relation :
    (reciprocalUnit R c : CommonBase R c)^2*originalT R c=
      algebraMap R (CommonBase R c) (c 0 : R) := by
  rw [originalT,polynomial_X]
  calc
    _ = k R c*((rootUnit R c : CommonBase R c)*
        (reciprocalUnit R c : CommonBase R c))^2 := by unfold k;ring
    _ = algebraMap R (CommonBase R c) (c 0 : R) := by
      rw [reciprocal_relation,k]
      rw [←map_pow,←map_mul]
      have he : (↑(c 0)⁻¹ : R)*(c 0 : R)^2=(c 0 : R) := by
        rw [pow_two,←mul_assoc,Units.inv_mul,one_mul]
      rw [he]

theorem infinity1_relation : originalT R c*infinity0 R c=infinity1 R c := by
  have hck : algebraMap R (CommonBase R c) (c 0 : R)*k R c=1 := by
    rw [k,←map_mul,Units.mul_inv,map_one]
  calc
    originalT R c*infinity0 R c =
        (4*twists R c*k R c^4*infinityInverse R c)*
          ((reciprocalUnit R c : CommonBase R c)^2*originalT R c*k R c) := by
      unfold infinity0;ring
    _ = infinity1 R c := by rw [reciprocal_square_relation,hck,mul_one];rfl

theorem coefficient1_transition : finite1 R c*derivativeFactor R c^2=infinity1 R c := by
  rw [finite1,mul_assoc,coefficient0_transition,infinity1_relation]
end IntegralOverlapCoefficients318
