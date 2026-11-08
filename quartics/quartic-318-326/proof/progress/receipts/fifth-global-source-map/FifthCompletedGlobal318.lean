module
public import FifthGlobalCompatibility318
public import CompletedCharacterGlobal318
public section
noncomputable section
namespace FifthCompletedGlobal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SourceTwistArithmetic318
open FifthCharacterShortPolynomial318
set_option maxHeartbeats 700000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Target:=WeierstrassGluing318.scheme A B
@[expose] def localMap:(b:Bool)→(ContactGlobalSmooth318.cover units).X b⟶Target
  | false=>FifthQuarticCompletedMap318.sourceMap
  | true=>FifthSourceInfinityScheme318.intoCompleted
lemma compatible (b d:Bool):
    pullback.fst ((ContactGlobalSmooth318.cover units).f b)
      ((ContactGlobalSmooth318.cover units).f d)≫localMap b=
    pullback.snd _ _≫localMap d:=by
  cases b <;> cases d
  · exact CompletedCharacterGlobal318.diagonal_compatibility
      (SourceGlobalAffine318.chartEmbedding units) FifthQuarticCompletedMap318.sourceMap
  · exact CompletedCharacterGlobal318.compatibility_of_actual_pullback
      (ContactFullOverlap318.actual_pullback units) _ _ FifthGlobalCompatibility318.maps_agree
  · exact CompletedCharacterGlobal318.compatibility_of_actual_pullback
      (ContactFullOverlap318.actual_pullback units).flip _ _ FifthGlobalCompatibility318.maps_agree.symm
  · exact CompletedCharacterGlobal318.diagonal_compatibility
      (InfinityGlobalScheme318.chartEmbedding units) FifthSourceInfinityScheme318.intoCompleted
/-- Actual fifth full-root quotient map from the entire original smooth proper
contact normalization to the completed rational short elliptic curve. -/
@[expose] def map:ContactGlobalSmooth318.Model units⟶Target:=
  (ContactGlobalSmooth318.cover units).glueMorphisms localMap compatible
@[reassoc] theorem on_finite:
    SourceGlobalAffine318.chartEmbedding units≫map=FifthQuarticCompletedMap318.sourceMap:=
  (ContactGlobalSmooth318.cover units).ι_glueMorphisms localMap compatible false
@[reassoc] theorem on_infinity:
    InfinityGlobalScheme318.chartEmbedding units≫map=FifthSourceInfinityScheme318.intoCompleted:=
  (ContactGlobalSmooth318.cover units).ι_glueMorphisms localMap compatible true
@[reassoc] theorem over_Q:map≫WeierstrassGluing318.structureMap A B=
    (ContactProjectiveModel318.coverMap units).fromNormalization≫ProjectiveJLine318.structureMap ℚ:=by
  apply (ContactGlobalSmooth318.cover units).hom_ext
  intro b
  cases b
  · change SourceGlobalAffine318.chartEmbedding units≫map≫_=_
    rw [←Category.assoc,on_finite,FifthQuarticCompletedMap318.source_over_Q]
    exact (SourceGlobalAffine318.chartEmbedding_over_Q units).symm
  · change InfinityGlobalScheme318.chartEmbedding units≫map≫_=_
    rw [←Category.assoc,on_infinity,FifthSourceInfinityScheme318.over_Q]
    exact (InfinityStructureSmooth318.chartEmbedding_over_Q units).symm
theorem unique (f:ContactGlobalSmooth318.Model units⟶Target)
    (hf:SourceGlobalAffine318.chartEmbedding units≫f=FifthQuarticCompletedMap318.sourceMap)
    (hi:InfinityGlobalScheme318.chartEmbedding units≫f=FifthSourceInfinityScheme318.intoCompleted):f=map:=by
  apply (ContactGlobalSmooth318.cover units).hom_ext
  intro b
  cases b
  · exact hf.trans on_finite.symm
  · exact hi.trans on_infinity.symm
end FifthCompletedGlobal318
