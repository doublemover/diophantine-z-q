module
public import FifthSourceInfinityAlgebra318
public import WeierstrassGluing318
public section
noncomputable section
namespace FifthSourceInfinityScheme318
open AlgebraicGeometry CategoryTheory
open SourceTwistArithmetic318 FifthCharacterShortPolynomial318 FifthSourceInfinityCoordinates318
open FifthSourceInfinityAlgebra318
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
@[expose] def scheme:Scheme:=Spec (CommRingCat.of I)
@[expose] def toFinite:scheme ⟶ ShortAffineScheme318.scheme A B:=
  Spec.map (CommRingCat.ofHom shortMap.toRingHom)
@[expose] def intoCompleted:scheme ⟶ WeierstrassGluing318.scheme A B:=
  toFinite ≫ WeierstrassGluing318.finiteChart A B
@[expose] def base:scheme ⟶ Spec (CommRingCat.of ℚ):=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ I))
@[reassoc] theorem over_Q : intoCompleted ≫ WeierstrassGluing318.structureMap A B=base:=by
  rw [intoCompleted,Category.assoc,WeierstrassGluing318.finiteChart_structure]
  change Spec.map (CommRingCat.ofHom shortMap.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ _))=_
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  exact shortMap.commutes q
/-- The actual regular map restricts to the specified fifth-character map
on the generic point of the original full contact function field. -/
@[reassoc] theorem generic_square :
    Spec.map (CommRingCat.ofHom embedding) ≫ intoCompleted=
      Spec.map (CommRingCat.ofHom rawMap) ≫ WeierstrassGluing318.finiteChart A B:=by
  rw [intoCompleted,←Category.assoc,toFinite,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (embedding.comp shortMap.toRingHom)) ≫ _=_
  rw [original_field_square]
end FifthSourceInfinityScheme318
