module
public import FifthCharacterShortAlgebra318
public section
noncomputable section
namespace FifthCharacterShortCoordinates318
open Polynomial QuadraticPresentation318 FifthCharacterShortPolynomial318 FifthCharacterShortAlgebra318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
@[expose] def u:CubicRing:=algebraMap ℚ[X] CubicRing X
@[expose] def v:CubicRing:=AdjoinRoot.root (polynomial FifthCharacterPolynomial318.reciprocal)
lemma root_on_polynomial (p:ℚ[X]):
    rootEquiv (algebraMap ℚ[X] CubicRing p)=algebraMap ℚ[X] ShortRoot (baseChange p):=by
  change (UnitRootScaling318.equiv _ _ rootScale changed_reciprocal) (changeBase (AdjoinRoot.of _ p))=_
  simp only [changeBase,AdjoinRoot.coe_mapAlgEquiv,AdjoinRoot.map_of]
  exact (UnitRootScaling318.equiv _ _ rootScale changed_reciprocal).commutes _
lemma root_on_v : rootEquiv v=algebraMap ℚ ShortRoot (↑yScale⁻¹:ℚ)*AdjoinRoot.root (polynomial shortPolynomial):=by
  change (UnitRootScaling318.equiv _ _ rootScale changed_reciprocal)
    (changeBase (AdjoinRoot.root (polynomial FifthCharacterPolynomial318.reciprocal)))=_
  simp only [changeBase,AdjoinRoot.coe_mapAlgEquiv,AdjoinRoot.map_root]
  change UnitRootScaling318.hom _ _ rootScale changed_reciprocal (AdjoinRoot.root _)=_
  rw [UnitRootScaling318.hom_root]
  rfl
lemma standard_on_polynomial (p:ℚ[X]):
    standardEquiv (algebraMap ℚ[X] ShortRoot p)=algebraMap ℚ[X] (AffineCoordinateDomain318.CoordinateRing A B) p:=by
  change AdjoinRoot.algEquivOfEq ℚ _ _ _ (AdjoinRoot.of _ p)=_
  simp only [AdjoinRoot.coe_algEquivOfEq,AdjoinRoot.coe_algHomOfDvd,AdjoinRoot.liftAlgHom_of]
  rfl
lemma standard_on_root : standardEquiv (AdjoinRoot.root (polynomial shortPolynomial))=
    AffineCoordinateDomain318.y A B:=AdjoinRoot.algEquivOfEq_root (R:=ℚ) _ _ _
/-- Exact forward images of the original reciprocal variables. -/
theorem coordinate_u : coordinateEquiv u=
    algebraMap ℚ _ (↑xScale⁻¹:ℚ)*ShortAffineJacobian318.x A B+
      algebraMap ℚ _ (-shift*(↑xScale⁻¹:ℚ)):=by
  simp only [u,coordinateEquiv,AlgEquiv.trans_apply,root_on_polynomial,standard_on_polynomial,
    baseChange_apply,Polynomial.X_comp,map_add,map_mul]
  change AffineCoordinateDomain318.backward A B
    (algebraMap ℚ (AffineCoordinateDomain318.CoordinateRing A B) (↑xScale⁻¹:ℚ))*
      AffineCoordinateDomain318.backward A B (AffineCoordinateDomain318.x A B)+
    AffineCoordinateDomain318.backward A B
      (algebraMap ℚ (AffineCoordinateDomain318.CoordinateRing A B) (-shift))*
    AffineCoordinateDomain318.backward A B
      (algebraMap ℚ (AffineCoordinateDomain318.CoordinateRing A B) (↑xScale⁻¹:ℚ))=_
  simp only [AlgHom.commutes,AffineCoordinateDomain318.backward_x]
theorem coordinate_v : coordinateEquiv v=
    algebraMap ℚ _ (↑yScale⁻¹:ℚ)*ShortAffineJacobian318.y A B:=by
  simp only [coordinateEquiv,AlgEquiv.trans_apply,root_on_v,map_mul,AlgEquiv.commutes,standard_on_root]
  change algebraMap ℚ (ShortAffineJacobian318.Ring A B) (↑yScale⁻¹:ℚ)*
    AffineCoordinateDomain318.backward A B (AffineCoordinateDomain318.y A B)=_
  rw [AffineCoordinateDomain318.backward_y]
/-- The inverse maps are the announced actual normalization coordinates. -/
theorem inverse_x : coordinateEquiv.symm (ShortAffineJacobian318.x A B)=
    algebraMap ℚ CubicRing (xScale:ℚ)*u+algebraMap ℚ CubicRing shift:=by
  apply coordinateEquiv.injective
  rw [AlgEquiv.apply_symm_apply,map_add,map_mul,AlgEquiv.commutes,coordinate_u,AlgEquiv.commutes]
  have hc:(xScale:ℚ)*(-shift*(↑xScale⁻¹:ℚ))+shift=0:=by
    norm_num [xScale,shift]
  symm
  calc
    _=(algebraMap ℚ _ (xScale:ℚ)*algebraMap ℚ _ (↑xScale⁻¹:ℚ))*ShortAffineJacobian318.x A B+
      algebraMap ℚ _ ((xScale:ℚ)*(-shift*(↑xScale⁻¹:ℚ))+shift):=by
        simp only [map_add,map_mul]
        ring
    _=ShortAffineJacobian318.x A B:=by
      rw [←map_mul,Units.mul_inv,map_one,one_mul,hc,map_zero,add_zero]
theorem inverse_y : coordinateEquiv.symm (ShortAffineJacobian318.y A B)=
    algebraMap ℚ CubicRing (yScale:ℚ)*v:=by
  apply coordinateEquiv.injective
  rw [AlgEquiv.apply_symm_apply,map_mul,AlgEquiv.commutes,coordinate_v,
    ←mul_assoc,←map_mul,Units.mul_inv,map_one,one_mul]
end FifthCharacterShortCoordinates318
