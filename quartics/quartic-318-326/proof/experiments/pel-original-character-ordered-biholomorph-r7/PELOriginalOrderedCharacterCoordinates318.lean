module
public import ThreeBranchLegendreAffineCoordinates318
public import PELOriginalOrderedCharacterSchemeMaps318
public section
noncomputable section
namespace PELOriginalOrderedCharacterCoordinates318
open Polynomial QuadraticPresentation318
open PELOriginalCommonContactBase318 PELOriginalActualCharacterFields318
open PELOriginalOrderedCharacterSchemeMaps318 PELOriginalWholeCharacterOrders318
set_option maxHeartbeats 800000

@[expose] def center (i:Fin 4):ℂ:=
  ThreeBranchLegendreInfinityAlgebra318.center (branch i 0) (branch i 1) (branch i 2)
@[expose] def difference (i:Fin 4):ℂ:=branch i 1-branch i 0
@[expose] def rootScale (i:Fin 4):ℂ:=
  ThreeBranchLegendrePolynomial318.rootScale (branch i 0) (branch i 1)
abbrev A (i:Fin 4):=NormalizedLegendreProjectiveModel318.A
  (PELOriginalOrderedCharacterCoordinate318.parameter i)
abbrev B (i:Fin 4):=NormalizedLegendreProjectiveModel318.B
  (PELOriginalOrderedCharacterCoordinate318.parameter i)
abbrev Target (i:Fin 4):=ShortAffineJacobian318.Ring (A i) (B i)
@[expose] def cubicT (i:Fin 4):Cubic i:=algebraMap ℂ[X] (Cubic i) X
@[expose] def cubicV (i:Fin 4):Cubic i:=
  AdjoinRoot.root (polynomial (FourRootCharacterPolynomialOrder318.radicand branches (omitted i)))

lemma coordinate_t (i:Fin 4):coordinateEquiv i (cubicT i)=
    algebraMap ℂ (Target i) (difference i)*ShortAffineJacobian318.x (A i) (B i)+
      algebraMap ℂ (Target i) (center i):=by
  have h: (ContactGenericFiber318.rootParameterEquiv (polynomial_eq i))
      (cubicT i)=algebraMap ℂ[X]
        (ThreeBranchLegendreAffineIso318.Cubic (branch i 0) (branch i 1) (branch i 2)) X:=
    (ContactGenericFiber318.rootParameterEquiv (polynomial_eq i)).commutes X
  simpa only [PELOriginalOrderedCharacterSchemeMaps318.coordinateEquiv,
    AlgEquiv.trans_apply,h,parameter_eq,difference,center] using
      ThreeBranchLegendreAffineCoordinates318.coordinate_t
        (branch i 0) (branch i 1) (branch i 2) (first_difference i)

lemma coordinate_v (i:Fin 4):coordinateEquiv i (cubicV i)=
    algebraMap ℂ (Target i) (rootScale i)*ShortAffineJacobian318.y (A i) (B i):=by
  simpa only [PELOriginalOrderedCharacterSchemeMaps318.coordinateEquiv,
    AlgEquiv.trans_apply,cubicV,ContactGenericFiber318.rootParameterEquiv_generator,
    parameter_eq,rootScale,ThreeBranchLegendreAffineCoordinates318.v] using
      ThreeBranchLegendreAffineCoordinates318.coordinate_v
        (branch i 0) (branch i 1) (branch i 2) (first_difference i)

lemma difference_ne_zero (i:Fin 4):difference i≠0:=sub_ne_zero.mpr (first_difference i)
lemma rootScale_ne_zero (i:Fin 4):rootScale i≠0:=
  ThreeBranchLegendrePolynomial318.rootScale_ne_zero _ _ (first_difference i)

lemma inverse_x (i:Fin 4):(coordinateEquiv i).symm (ShortAffineJacobian318.x (A i) (B i))=
    algebraMap ℂ (Cubic i) (difference i)⁻¹*(cubicT i-algebraMap ℂ (Cubic i) (center i)):=by
  apply (coordinateEquiv i).injective
  rw [AlgEquiv.apply_symm_apply,map_mul,map_sub,AlgEquiv.commutes,AlgEquiv.commutes,coordinate_t]
  have h:algebraMap ℂ (Target i) (difference i)⁻¹*algebraMap ℂ (Target i) (difference i)=1:=by
    rw [←map_mul,inv_mul_cancel₀ (difference_ne_zero i),map_one]
  calc
    _=(algebraMap ℂ (Target i) (difference i)⁻¹*algebraMap ℂ (Target i) (difference i))*
      ShortAffineJacobian318.x (A i) (B i):=by rw [h,one_mul]
    _=_:=by ring

lemma inverse_y (i:Fin 4):(coordinateEquiv i).symm (ShortAffineJacobian318.y (A i) (B i))=
    algebraMap ℂ (Cubic i) (rootScale i)⁻¹*cubicV i:=by
  apply (coordinateEquiv i).injective
  rw [AlgEquiv.apply_symm_apply,map_mul,AlgEquiv.commutes,coordinate_v]
  rw [←mul_assoc,←map_mul,inv_mul_cancel₀ (rootScale_ne_zero i),map_one,one_mul]

/-- Whole-ring formulas for the SAME previously constructed finite map.
These bind the affine chart to the exact ordinate scale used at infinity. -/
lemma finite_x (i:Fin 4):mapOnRings i (ShortAffineJacobian318.x (A i) (B i))=
    algebraMap ℂ (FourRootAffineCoordinateRing318.Ring branches) (difference i)⁻¹*
      (FourRootAffineCoordinateRing318.coordinate branches none-
        algebraMap ℂ (FourRootAffineCoordinateRing318.Ring branches) (center i)):=by
  rw [mapOnRings,AlgHom.comp_apply,inverse_x,map_mul,map_sub,AlgHom.commutes,AlgHom.commutes]
  congr 2
  change FourRootCharacterWholeAffineMap318.toSource branches branches_injective _ _
    (algebraMap ℂ[X] (Cubic i) X)=_
  rw [AlgHom.commutes]
  exact Polynomial.aeval_X _

lemma finite_y (i:Fin 4):mapOnRings i (ShortAffineJacobian318.y (A i) (B i))=
    algebraMap ℂ (FourRootAffineCoordinateRing318.Ring branches) (rootScale i)⁻¹*
      ∏k∈omitted i,FourRootAffineCoordinateRing318.coordinate branches (some k):=by
  rw [mapOnRings,AlgHom.comp_apply,inverse_y,map_mul,AlgHom.commutes]
  congr 1
  exact FourRootCharacterWholeAffineMap318.on_root branches branches_injective _ _

lemma finite_y_three (i:Fin 4):mapOnRings i (ShortAffineJacobian318.y (A i) (B i))=
    algebraMap ℂ (FourRootAffineCoordinateRing318.Ring branches) (rootScale i)⁻¹*
      (FourRootAffineCoordinateRing318.coordinate branches (some (SourceTwistArithmetic318.complement i 0))*
       FourRootAffineCoordinateRing318.coordinate branches (some (SourceTwistArithmetic318.complement i 1))*
       FourRootAffineCoordinateRing318.coordinate branches (some (SourceTwistArithmetic318.complement i 2))):=by
  rw [finite_y,omitted_eq]
  fin_cases i <;> simp [SourceTwistArithmetic318.complement] <;> ring
end PELOriginalOrderedCharacterCoordinates318
