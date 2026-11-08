module
public import AffineRationalScaling318
public import CharacterPublishedModels318
public section
noncomputable section
namespace PublishedCharacterScheme318
open SourceTwistArithmetic318 CharacterPublishedModels318 CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] def coordinateEquiv (i:Fin 4):
    ShortAffineJacobian318.Ring (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i)≃ₐ[ℚ]
    ShortAffineJacobian318.Ring (publishedA i) (publishedB i):=
  AffineRationalScaling318.equiv _ _ _ _ (scaleUnit i)
    (published_scaled_exact i).1 (published_scaled_exact i).2

/-- Actual affine Scheme isomorphism with each literal published model. -/
@[expose] def affineIso (i:Fin 4):
    ShortAffineScheme318.scheme (publishedA i) (publishedB i)≅
    ShortAffineScheme318.scheme (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i):=
  Scheme.Spec.mapIso (coordinateEquiv i).toRingEquiv.toCommRingCatIso.op

theorem affineIso_over_Q (i:Fin 4):
    (affineIso i).hom≫ShortAffineScheme318.structureMap
      (twistProducts i^2*cubicA i) (twistProducts i^3*cubicB i)=
    ShortAffineScheme318.structureMap (publishedA i) (publishedB i):=by
  change Spec.map (CommRingCat.ofHom (coordinateEquiv i).toRingHom)≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ _))=_
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  exact (coordinateEquiv i).commutes q
end PublishedCharacterScheme318
