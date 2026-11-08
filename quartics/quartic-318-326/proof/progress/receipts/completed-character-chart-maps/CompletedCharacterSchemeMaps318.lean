module
public import CompletedCharacterOverlap318
public import SourceCharacterAffine318
public import WeierstrassGluing318
public import ContactFullOverlap318
import all WeierstrassGluing318
public section
noncomputable section
namespace CompletedCharacterSchemeMaps318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SourceTwistArithmetic318
open CompletedCharacterOverlap318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Target (i:Fin 4):=WeierstrassGluing318.scheme (publishedA i) (publishedB i)
@[expose] def finiteChartMap (i:Fin 4):
    Spec (CommRingCat.of SourceCharacterAlgebra318.Source)⟶Target i:=
  SourceCharacterAffine318.publishedMap i≫WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)
@[expose] def infinityChartMap (i:Fin 4):
    Spec (CommRingCat.of CompletedCharacterInfinity318.I)⟶Target i:=
  Spec.map (CommRingCat.ofHom (CompletedCharacterInfinity318.infinityMap i).toRingHom)≫
    WeierstrassGluing318.infinityChart (publishedA i) (publishedB i)
@[expose] def overlapSchemeMap (i:Fin 4):Spec (CommRingCat.of O)⟶
    WeierstrassGluing318.overlap (publishedA i) (publishedB i):=
  Spec.map (CommRingCat.ofHom ((overlapMap i).comp
    (WeierstrassOverlap318.overlapEquiv (publishedA i) (publishedB i)).toAlgHom).toRingHom)

lemma overlap_finite (i:Fin 4):
    overlapSchemeMap i≫WeierstrassGluing318.intoAffine (publishedA i) (publishedB i)=
      Spec.map (CommRingCat.ofHom (finiteMap i).toRingHom):=by
  unfold overlapSchemeMap WeierstrassGluing318.intoAffine
  rw [←Spec.map_comp_assoc,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change overlapMap i ((WeierstrassOverlap318.overlapEquiv (publishedA i) (publishedB i))
    ((WeierstrassOverlap318.overlapEquiv (publishedA i) (publishedB i)).symm
      (algebraMap (CompletedCharacterInfinity318.Published i) _ a)))=finiteMap i a
  rw [AlgEquiv.apply_symm_apply,overlapMap_on_finite]

lemma overlap_infinity (i:Fin 4):
    overlapSchemeMap i≫WeierstrassGluing318.intoInfinity (publishedA i) (publishedB i)=
      Spec.map (CommRingCat.ofHom (infinityMap i).toRingHom):=by
  unfold overlapSchemeMap WeierstrassGluing318.intoInfinity
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change overlapMap i (WeierstrassOverlap318.toAffine (publishedA i) (publishedB i)
    (algebraMap (InfinityChart318.Ring (publishedA i) (publishedB i)) _ a))=infinityMap i a
  rw [WeierstrassOverlap318.toAffine_map]
  exact DFunLike.congr_fun (infinity_compatibility i) a

lemma source_restriction (i:Fin 4):ContactOverlapMaps318.sourceInclusion units≫finiteChartMap i=
    Spec.map (CommRingCat.ofHom (finiteMap i).toRingHom)≫
      WeierstrassGluing318.finiteChart (publishedA i) (publishedB i):=by
  unfold ContactOverlapMaps318.sourceInclusion finiteChartMap SourceCharacterAffine318.publishedMap
  rw [←Spec.map_comp_assoc]
  rfl

lemma infinity_restriction (i:Fin 4):ContactOverlapMaps318.infinityInclusion units≫infinityChartMap i=
    Spec.map (CommRingCat.ofHom (infinityMap i).toRingHom)≫
      WeierstrassGluing318.infinityChart (publishedA i) (publishedB i):=by
  unfold ContactOverlapMaps318.infinityInclusion infinityChartMap
  rw [←Spec.map_comp_assoc]
  rfl

/-- The actual two source-chart morphisms into the literal completed
elliptic scheme agree on their entire specified common open. -/
theorem maps_agree (i:Fin 4):
    ContactOverlapMaps318.sourceInclusion units≫finiteChartMap i=
      ContactOverlapMaps318.infinityInclusion units≫infinityChartMap i:=by
  rw [source_restriction,infinity_restriction,←overlap_finite,←overlap_infinity,Category.assoc,Category.assoc]
  exact congrArg (fun f=>overlapSchemeMap i≫f)
    (pushout.condition (f:=WeierstrassGluing318.intoAffine (publishedA i) (publishedB i))
      (g:=WeierstrassGluing318.intoInfinity (publishedA i) (publishedB i)))

lemma finite_over_Q (i:Fin 4):finiteChartMap i≫WeierstrassGluing318.structureMap (publishedA i) (publishedB i)=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ SourceCharacterAlgebra318.Source)):=by
  rw [finiteChartMap,Category.assoc,WeierstrassGluing318.finiteChart_structure]
  exact SourceCharacterAffine318.publishedMap_over_Q i

lemma infinity_over_Q (i:Fin 4):infinityChartMap i≫WeierstrassGluing318.structureMap (publishedA i) (publishedB i)=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ CompletedCharacterInfinity318.I)):=by
  rw [infinityChartMap,Category.assoc,WeierstrassGluing318.infinityChart_structure]
  unfold InfinitySmooth318.structureMap
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  exact (CompletedCharacterInfinity318.infinityMap i).commutes q
end CompletedCharacterSchemeMaps318
