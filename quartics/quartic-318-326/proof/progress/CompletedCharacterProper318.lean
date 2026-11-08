module
public import CompletedCharacterGlobal318
public import CubicClosedImmersion318
public import CompletedIntegral318
public section
noncomputable section
namespace CompletedCharacterProper318
open CategoryTheory AlgebraicGeometry SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Properness is relative to the actual Q-structures on both existing models. -/
theorem completedMap_proper (i:Fin 4):IsProper (completedMap i):=by
  letI:=CubicClosedImmersion318.structure_separated (publishedA i) (publishedB i)
  letI:IsProper (completedMap i≫WeierstrassGluing318.structureMap (publishedA i) (publishedB i)):=by
    rw [over_Q]
    exact (ContactGlobalProper318.proper_integral_extension units).2.2
  exact IsProper.of_comp (completedMap i) (WeierstrassGluing318.structureMap (publishedA i) (publishedB i))

/-- Dominance uses the actual surjective finite source-character map and
density of the nonempty finite chart in the actual integral completed target. -/
theorem completedMap_dominant (i:Fin 4):IsDominant (completedMap i):=by
  letI:Surjective (SourceCharacterAffine318.publishedMap i):=
    ⟨SourceCharacterAffine318.publishedMap_surjective i⟩
  letI:=CompletedIntegral318.completed_irreducible (publishedA i) (publishedB i)
  letI:=AffineCoordinateDomain318.affine_domain (publishedA i) (publishedB i)
  letI:Nonempty (ShortAffineScheme318.scheme (publishedA i) (publishedB i)):=by
    change Nonempty (Spec (CommRingCat.of (ShortAffineJacobian318.Ring (publishedA i) (publishedB i))))
    infer_instance
  letI:IsDominant (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)):=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
      (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i)).isOpenEmbedding.isOpenMap⟩
  letI:IsDominant (SourceGlobalAffine318.chartEmbedding units≫completedMap i):=by
    rw [on_finite,finiteChartMap]
    infer_instance
  exact IsDominant.of_comp (SourceGlobalAffine318.chartEmbedding units) (completedMap i)

/-- Every point of the actual completed target is attained. -/
theorem completedMap_surjective (i:Fin 4):Surjective (completedMap i):=by
  letI:=completedMap_proper i
  letI:=completedMap_dominant i
  infer_instance

theorem target_smooth (i:Fin 4):Smooth (WeierstrassGluing318.structureMap (publishedA i) (publishedB i)):=
  WeierstrassGluing318.structure_smooth _ _ (isUnit_iff_ne_zero.mpr
    (mul_ne_zero (by norm_num) (published_nonsingular i)))

theorem target_proper_integral (i:Fin 4):
    IsProper (WeierstrassGluing318.structureMap (publishedA i) (publishedB i))∧IsIntegral (Target i):=
  ⟨CubicClosedImmersion318.structure_proper _ _,CompletedIntegral318.completed_integral _ _⟩
end CompletedCharacterProper318
