module
public import CompletedCharacterFinite318
public import CubicCompletedNormalization318
public section
noncomputable section
namespace CompletedCharacterNormalizationJoin318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterFinite318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual canonical comparison, with no unfilled affine-transform
premise, from the earlier character normalization to the completed curve. -/
@[expose] def comparison (i:Fin 4):SourceCharacterGlobal318.Model i⟶Target i:=
  CubicCompletedNormalization318.comparison i (affineTransform i)
    (affineTransform_chart i) (affineTransform_over_Q i)
lemma comparison_on_cubic (i:Fin 4):
    (SourceCharacterGlobal318.coverMap i).toNormalization≫comparison i=CubicCompletedAffine318.embedding i:=
  CubicCompletedNormalization318.on_cubic i (affineTransform i)
    (affineTransform_chart i) (affineTransform_over_Q i)
lemma comparison_over_line (i:Fin 4):comparison i≫targetTMap i=SourceCharacterGlobal318.modelMap i:=
  CubicCompletedNormalization318.over_line i (affineTransform i)
    (affineTransform_chart i) (affineTransform_over_Q i)
theorem comparison_integral (i:Fin 4):IsIntegralHom (comparison i):=
  CubicCompletedNormalization318.comparison_integral i (affineTransform i)
    (affineTransform_chart i) (affineTransform_over_Q i)

lemma completedMap_on_original (i:Fin 4):
    ContactProjectiveModel318.sourceOpen units≫completedMap i=
      SourceCharacterGlobal318.originalToCubic i≫CubicCompletedAffine318.embedding i:=by
  rw [←ContactOverlapMaps318.source_square,Category.assoc,on_finite,finiteChartMap,CubicCompletedAffine318.embedding]
  change Spec.map (CommRingCat.ofHom (SourceOpenFractionField318.orderToOpen units))≫
      Spec.map (CommRingCat.ofHom (SourceCharacterAlgebra318.publishedToSource i).toRingHom)≫
        WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)=
    Spec.map (CommRingCat.ofHom ((SourceOpenFractionField318.orderToOpen units).comp
      (SourceCharacterAlgebra318.toSource i).toRingHom))≫
      Spec.map (CommRingCat.ofHom (CubicPublishedScheme318.coordinateEquiv i).symm.toRingHom)≫
        WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)
  rw [←Spec.map_comp_assoc,←Spec.map_comp_assoc]
  congr 2

/-- The old and completed character constructions commute through the
actual canonical comparison on the entire original contact normalization. -/
theorem original_global_join (i:Fin 4):
    SourceCharacterGlobal318.globalMap i≫comparison i=completedMap i:=by
  letI:=targetTMap_finite i
  apply Scheme.Hom.normalization.hom_ext (ContactProjectiveModel318.coverMap units)
    _ _ (targetTMap i)
  · change ContactProjectiveModel318.sourceOpen units≫(SourceCharacterGlobal318.globalMap i≫comparison i)=_
    rw [←Category.assoc,SourceCharacterGlobal318.globalMap_on_original,Category.assoc,
      comparison_on_cubic]
    exact (completedMap_on_original i).symm
  · rw [Category.assoc,comparison_over_line,SourceCharacterGlobal318.globalMap_over_line]
    rfl
  · exact completedMap_over_t i

/-- Every completed-target point is hit by this actual integral comparison.
No isomorphism or inverse is inferred from its dense affine restriction. -/
theorem comparison_surjective (i:Fin 4):Surjective (comparison i):=by
  letI:=CompletedCharacterProper318.completedMap_surjective i
  constructor
  intro y
  obtain ⟨x,hx⟩:=(completedMap i).surjective y
  refine ⟨SourceCharacterGlobal318.globalMap i x,?_⟩
  change (SourceCharacterGlobal318.globalMap i≫comparison i) x=y
  rw [original_global_join]
  exact hx
end CompletedCharacterNormalizationJoin318
