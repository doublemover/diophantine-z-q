module
public import SourceCharacterAlgebra318
public section
noncomputable section
namespace SourceCharacterAffine318
open CategoryTheory AlgebraicGeometry SourceTwistArithmetic318 SourceCharacterAlgebra318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] def cubicMap (i:Fin 4):Spec (CommRingCat.of Source)⟶Spec (CommRingCat.of (Cubic i)):=
  Spec.map (CommRingCat.ofHom (toSource i).toRingHom)
instance cubicMap_finite (i:Fin 4):IsFinite (cubicMap i):=
  IsFinite.SpecMap_iff.mpr (toSource_finite i)
theorem cubicMap_surjective (i:Fin 4):Function.Surjective (cubicMap i):=
  (toSource_finite i).isIntegral.comap_surjective (toSource_injective i)
theorem cubicMap_over_base (i:Fin 4):
    cubicMap i≫Spec.map (CommRingCat.ofHom (algebraMap R (Cubic i)))=
      Spec.map (CommRingCat.ofHom (algebraMap R Source)):=by
  rw [cubicMap,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact (toSource i).commutes p

@[expose] def publishedMap (i:Fin 4):Spec (CommRingCat.of Source)⟶
    ShortAffineScheme318.scheme (publishedA i) (publishedB i):=
  Spec.map (CommRingCat.ofHom (publishedToSource i).toRingHom)
instance publishedMap_finite (i:Fin 4):IsFinite (publishedMap i):=
  IsFinite.SpecMap_iff.mpr (publishedToSource_finite i)
theorem publishedMap_surjective (i:Fin 4):Function.Surjective (publishedMap i):=
  (publishedToSource_finite i).isIntegral.comap_surjective (publishedToSource_injective i)
theorem publishedMap_over_Q (i:Fin 4):
    publishedMap i≫ShortAffineScheme318.structureMap (publishedA i) (publishedB i)=
      Spec.map (CommRingCat.ofHom (algebraMap ℚ Source)):=by
  change Spec.map (CommRingCat.ofHom (publishedToSource i).toRingHom)≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ _))=_
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  exact (publishedToSource i).commutes q
end SourceCharacterAffine318
