module
public import CubicCoordinateValues318
public import SourceCharacterAlgebra318
public section
noncomputable section
namespace CubicInverseCoordinates318
open Polynomial QuadraticPresentation318 SourceTwistArithmetic318 CubicWeierstrassPolynomial318
open CubicWeierstrassAlgebra318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma cancel_scale {S:Type*} [CommRing S] [Algebra ℚ S] (d q:ℚˣ) (n:ℕ) (x:S):
    algebraMap ℚ S (↑(d*(q⁻¹)^n):ℚ)*
      (algebraMap ℚ S (↑d⁻¹:ℚ)*(algebraMap ℚ S (q:ℚ))^n*x)=x:=by
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,map_mul,map_pow]
  calc
    _=(algebraMap ℚ S (d:ℚ)*algebraMap ℚ S (↑d⁻¹:ℚ))*
        ((algebraMap ℚ S (↑q⁻¹:ℚ)*algebraMap ℚ S (q:ℚ))^n)*x:=by
      rw [mul_pow]
      ring
    _=x:=by rw [←map_mul,Units.mul_inv,map_one,←map_mul,Units.inv_mul,map_one,one_pow,one_mul,one_mul]

@[expose] def xScale (i:Fin 4):ℚˣ:=twistUnit i*(CharacterPublishedModels318.scaleUnit i)⁻¹^2
@[expose] def yScale (i:Fin 4):ℚˣ:=twistUnit i*(CharacterPublishedModels318.scaleUnit i)⁻¹^3

/-- The inverse of the existing actual affine comparison sends published
x to this exact scaled and translated original t, not an arbitrary root. -/
theorem inverse_x (i:Fin 4):
    (CubicPublishedScheme318.coordinateEquiv i).symm (ShortAffineJacobian318.x (publishedA i) (publishedB i))=
      algebraMap ℚ (CubicRing i) (xScale i:ℚ)*
        (algebraMap ℚ[X] (CubicRing i) X-algebraMap ℚ (CubicRing i) (centroid i)):=by
  apply (CubicPublishedScheme318.coordinateEquiv i).injective
  rw [AlgEquiv.apply_symm_apply,map_mul,map_sub,AlgEquiv.commutes,
    CubicCoordinateValues318.published_x,AlgEquiv.commutes,add_sub_cancel_right]
  exact (cancel_scale (twistUnit i) (CharacterPublishedModels318.scaleUnit i) 2 _).symm

/-- The exact inverse y coordinate retains its complementary-root product
and its full rational scaling, including the cube of the published scale. -/
theorem inverse_y (i:Fin 4):
    (CubicPublishedScheme318.coordinateEquiv i).symm (ShortAffineJacobian318.y (publishedA i) (publishedB i))=
      algebraMap ℚ (CubicRing i) (yScale i:ℚ)*AdjoinRoot.root (polynomial (radicand i)):=by
  apply (CubicPublishedScheme318.coordinateEquiv i).injective
  rw [AlgEquiv.apply_symm_apply,map_mul,AlgEquiv.commutes,CubicCoordinateValues318.published_y]
  exact (cancel_scale (twistUnit i) (CharacterPublishedModels318.scaleUnit i) 3 _).symm

/-- These are the functions of the already constructed actual finite
source-character morphism, under its original SourceOrder embedding. -/
theorem source_x (i:Fin 4):
    SourceCharacterAlgebra318.publishedToSource i (ShortAffineJacobian318.x (publishedA i) (publishedB i))=
      algebraMap ℚ SourceCharacterAlgebra318.Source (xScale i:ℚ)*
        (algebraMap ℚ[X] SourceCharacterAlgebra318.Source X-
          algebraMap ℚ SourceCharacterAlgebra318.Source (centroid i)):=by
  change (SourceCharacterAlgebra318.toSource i).restrictScalars ℚ
    ((CubicPublishedScheme318.coordinateEquiv i).symm _)=_
  rw [inverse_x,map_mul,map_sub,AlgHom.commutes,AlgHom.commutes]
  congr 1
  exact congrArg (fun x=>x-algebraMap ℚ SourceCharacterAlgebra318.Source (centroid i))
    ((SourceCharacterAlgebra318.toSource i).commutes X)

theorem source_y (i:Fin 4):
    SourceCharacterAlgebra318.publishedToSource i (ShortAffineJacobian318.y (publishedA i) (publishedB i))=
      algebraMap ℚ SourceCharacterAlgebra318.Source (yScale i:ℚ)*
        SourceCharacterAlgebra318.toSource i (AdjoinRoot.root (polynomial (radicand i))):=by
  change (SourceCharacterAlgebra318.toSource i).restrictScalars ℚ
    ((CubicPublishedScheme318.coordinateEquiv i).symm _)=_
  rw [inverse_y,map_mul,AlgHom.commutes]
  rfl
end CubicInverseCoordinates318
