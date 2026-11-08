module
public import CubicPublishedScheme318
public section
noncomputable section
namespace CubicCoordinateValues318
open Polynomial QuadraticPresentation318 SourceTwistArithmetic318 CubicWeierstrassPolynomial318
open CubicWeierstrassAlgebra318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma rootEquiv_on_polynomial (i:Fin 4) (p:ℚ[X]):
    rootEquiv i (algebraMap ℚ[X] (CubicRing i) p)=
      algebraMap ℚ[X] (ShortRoot i) (baseChange i p):=by
  change (UnitRootScaling318.equiv _ _ (scaleUnit i) (changed_radicand i))
    (changeBase i (AdjoinRoot.of _ p))=_
  simp only [changeBase,AdjoinRoot.coe_mapAlgEquiv,AdjoinRoot.map_of]
  exact (UnitRootScaling318.equiv _ _ (scaleUnit i) (changed_radicand i)).commutes _

lemma rootEquiv_root (i:Fin 4):
    rootEquiv i (AdjoinRoot.root (polynomial (radicand i)))=
      algebraMap ℚ (ShortRoot i) (↑(twistUnit i)⁻¹:ℚ)*
        AdjoinRoot.root (polynomial (shortPolynomial i)):=by
  change (UnitRootScaling318.equiv _ _ (scaleUnit i) (changed_radicand i))
    (changeBase i (AdjoinRoot.root (polynomial (radicand i))))=_
  simp only [changeBase,AdjoinRoot.coe_mapAlgEquiv,AdjoinRoot.map_root]
  change UnitRootScaling318.hom (baseChange i (radicand i)) (shortPolynomial i)
    (scaleUnit i) (changed_radicand i)
    (AdjoinRoot.root (polynomial (baseChange i (radicand i))))=_
  rw [UnitRootScaling318.hom_root]
  rfl

lemma standardEquiv_on_polynomial (i:Fin 4) (p:ℚ[X]):
    standardEquiv i (algebraMap ℚ[X] (ShortRoot i) p)=
      algebraMap ℚ[X]
        (AffineCoordinateDomain318.CoordinateRing (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i)) p:=by
  change AdjoinRoot.algEquivOfEq ℚ _ _ _ (AdjoinRoot.of _ p)=_
  simp only [AdjoinRoot.coe_algEquivOfEq,AdjoinRoot.coe_algHomOfDvd,AdjoinRoot.liftAlgHom_of]
  rfl

lemma standardEquiv_root (i:Fin 4):
    standardEquiv i (AdjoinRoot.root (polynomial (shortPolynomial i)))=
      AffineCoordinateDomain318.y (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i):=
  AdjoinRoot.algEquivOfEq_root (R:=ℚ) _ _ _

lemma character_x (i:Fin 4):
    CubicWeierstrassAlgebra318.coordinateEquiv i (algebraMap ℚ[X] (CubicRing i) X)=
      algebraMap ℚ _ (↑(twistUnit i)⁻¹:ℚ)*
        ShortAffineJacobian318.x (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i)+
      algebraMap ℚ _ (centroid i):=by
  simp only [CubicWeierstrassAlgebra318.coordinateEquiv,AlgEquiv.trans_apply,
    rootEquiv_on_polynomial,standardEquiv_on_polynomial,baseChange_apply,Polynomial.X_comp]
  simp only [map_add,map_mul]
  change AffineCoordinateDomain318.backward (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i)
    (algebraMap ℚ (AffineCoordinateDomain318.CoordinateRing (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i)) (↑(twistUnit i)⁻¹:ℚ))*
      AffineCoordinateDomain318.backward (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i) (AffineCoordinateDomain318.x (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i))+
      AffineCoordinateDomain318.backward (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i) (algebraMap ℚ (AffineCoordinateDomain318.CoordinateRing (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i)) (centroid i))=_
  rw [AlgHom.commutes,AlgHom.commutes,AffineCoordinateDomain318.backward_x]

lemma character_y (i:Fin 4):
    CubicWeierstrassAlgebra318.coordinateEquiv i (AdjoinRoot.root (polynomial (radicand i)))=
      algebraMap ℚ _ (↑(twistUnit i)⁻¹:ℚ)*
        ShortAffineJacobian318.y (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i):=by
  simp only [CubicWeierstrassAlgebra318.coordinateEquiv,AlgEquiv.trans_apply,
    rootEquiv_root,map_mul,AlgEquiv.commutes,standardEquiv_root]
  change algebraMap ℚ (ShortAffineJacobian318.Ring (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i)) (↑(twistUnit i)⁻¹:ℚ)*
    AffineCoordinateDomain318.backward (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i) (AffineCoordinateDomain318.y (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i))=_
  rw [AffineCoordinateDomain318.backward_y]

/-- Exact images of both cubic coordinates under the already constructed
published affine algebra equivalence, including all rational scale factors. -/
theorem published_x (i:Fin 4):
    CubicPublishedScheme318.coordinateEquiv i (algebraMap ℚ[X] (CubicRing i) X)=
      algebraMap ℚ _ (↑(twistUnit i)⁻¹:ℚ)*
        (algebraMap ℚ _ (coordinateScale i))^2*ShortAffineJacobian318.x (publishedA i) (publishedB i)+
      algebraMap ℚ _ (centroid i):=by
  change PublishedCharacterScheme318.coordinateEquiv i
    (CubicWeierstrassAlgebra318.coordinateEquiv i _) = _
  rw [character_x,map_add,map_mul,AlgEquiv.commutes,AlgEquiv.commutes]
  change _*AffineRationalScaling318.hom (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i) (publishedA i) (publishedB i)
      (CharacterPublishedModels318.scaleUnit i) (published_scaled_exact i).1 (published_scaled_exact i).2
    (ShortAffineJacobian318.x _ _)+_=_
  rw [AffineRationalScaling318.hom_x]
  exact (mul_assoc _ _ _).symm |> congrArg (fun x=>x+algebraMap ℚ _ (centroid i))

theorem published_y (i:Fin 4):
    CubicPublishedScheme318.coordinateEquiv i (AdjoinRoot.root (polynomial (radicand i)))=
      algebraMap ℚ _ (↑(twistUnit i)⁻¹:ℚ)*
        (algebraMap ℚ _ (coordinateScale i))^3*ShortAffineJacobian318.y (publishedA i) (publishedB i):=by
  change PublishedCharacterScheme318.coordinateEquiv i
    (CubicWeierstrassAlgebra318.coordinateEquiv i _) = _
  rw [character_y,map_mul,AlgEquiv.commutes]
  change _*AffineRationalScaling318.hom (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i) (publishedA i) (publishedB i)
      (CharacterPublishedModels318.scaleUnit i) (published_scaled_exact i).1 (published_scaled_exact i).2
    (ShortAffineJacobian318.y _ _)=_
  rw [AffineRationalScaling318.hom_y]
  exact (mul_assoc _ _ _).symm
end CubicCoordinateValues318
