module
public import CubicWeierstrassAlgebra318
public import PublishedCharacterScheme318
public import SourceCharacterFields318
public section
noncomputable section
namespace CubicPublishedScheme318
open SourceTwistArithmetic318 CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The source of the algebra comparison is the literal cubic radicand
already proved for the actual character field in the original contact field. -/
theorem literal_radicand (i:Fin 4):CubicWeierstrassPolynomial318.radicand i=
    Polynomial.C (SourceCharacterFields318.twistProduct units i)*cubic i:=by
  rw [SourceCharacterFields318.fixed_twist_product]
  rfl

@[expose] def coordinateEquiv (i:Fin 4):CubicWeierstrassAlgebra318.CubicRing i≃ₐ[ℚ]
    ShortAffineJacobian318.Ring (publishedA i) (publishedB i):=
  (CubicWeierstrassAlgebra318.coordinateEquiv i).trans (PublishedCharacterScheme318.coordinateEquiv i)

/-- The actual affine cubic character presentation is isomorphic over Q
to the literal published affine Weierstrass model. -/
@[expose] def affineIso (i:Fin 4):
    ShortAffineScheme318.scheme (publishedA i) (publishedB i)≅
      Spec (CommRingCat.of (CubicWeierstrassAlgebra318.CubicRing i)):=
  Scheme.Spec.mapIso (coordinateEquiv i).toRingEquiv.toCommRingCatIso.op

theorem affineIso_over_Q (i:Fin 4):
    (affineIso i).hom≫Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (CubicWeierstrassAlgebra318.CubicRing i)))=
    ShortAffineScheme318.structureMap (publishedA i) (publishedB i):=by
  change Spec.map (CommRingCat.ofHom (coordinateEquiv i).toRingHom)≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ _))=_
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  exact (coordinateEquiv i).commutes q
end CubicPublishedScheme318
