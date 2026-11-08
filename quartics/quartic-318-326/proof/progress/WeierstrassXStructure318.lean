module
public import WeierstrassXProjection318
public import CubicClosedImmersion318
import all WeierstrassGluing318
public section
noncomputable section
namespace WeierstrassXStructure318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open WeierstrassReciprocalCoordinate318 WeierstrassReciprocalOverlap318 WeierstrassXProjection318
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R:Type u} [CommRing R] (A B:R)

lemma eval_over_base {S:Type u} [CommRing S] [Algebra R S] (v:S) (j:Fin 2):
    (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R) v).toRingHom)≫JLineAtlas318.chart R j)≫
      ProjectiveJLine318.structureMap R=Spec.map (CommRingCat.ofHom (algebraMap R S)):=by
  rw [Category.assoc,JLineAtlas318.chart_over_base,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (Polynomial.aeval (R:=R) v).commutes r

lemma infinityProjection_over_base:
    infinityProjection A B≫ProjectiveJLine318.structureMap R=InfinitySmooth318.structureMap A B:=by
  apply (cover A B).hom_ext
  intro b
  cases b
  · change WeierstrassGluing318.intoInfinity A B≫infinityProjection A B≫_=
      WeierstrassGluing318.intoInfinity A B≫InfinitySmooth318.structureMap A B
    rw [←Category.assoc,infinityProjection_overlap]
    unfold overlapProjection
    rw [eval_over_base]
    unfold WeierstrassGluing318.intoInfinity InfinitySmooth318.structureMap
    rw [←Spec.map_comp]
    congr 1
  · change nearBase A B≫infinityProjection A B≫_=
      nearBase A B≫InfinitySmooth318.structureMap A B
    rw [←Category.assoc,infinityProjection_near]
    unfold nearProjection
    rw [eval_over_base]
    unfold nearBase InfinitySmooth318.structureMap
    rw [←Spec.map_comp]
    congr 1

/-- The actual complete x-coordinate morphism has the original R-structure square. -/
theorem xMap_over_base:
    xMap A B≫ProjectiveJLine318.structureMap R=WeierstrassGluing318.structureMap A B:=by
  apply pushout.hom_ext
  · change WeierstrassGluing318.finiteChart A B≫(xMap A B≫_)=
      WeierstrassGluing318.finiteChart A B≫WeierstrassGluing318.structureMap A B
    rw [←Category.assoc,finiteChart_xMap,WeierstrassGluing318.finiteChart_structure]
    exact eval_over_base (ShortAffineJacobian318.x A B) 1
  · change WeierstrassGluing318.infinityChart A B≫(xMap A B≫_)=
      WeierstrassGluing318.infinityChart A B≫WeierstrassGluing318.structureMap A B
    rw [←Category.assoc,infinityChart_xMap,WeierstrassGluing318.infinityChart_structure]
    exact infinityProjection_over_base A B

/-- Separatedness refers to this actual x-coordinate morphism, by its exact
factorization of the existing separated R-structure morphism. -/
theorem xMap_separated:IsSeparated (xMap A B):=by
  haveI:IsSeparated (xMap A B≫ProjectiveJLine318.structureMap R):=by
    rw [xMap_over_base]
    exact CubicClosedImmersion318.structure_separated A B
  exact IsSeparated.of_comp (xMap A B) (ProjectiveJLine318.structureMap R)
end WeierstrassXStructure318
