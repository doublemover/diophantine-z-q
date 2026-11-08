module
public import CompletedCharacterBaseComparison318
public import ProperFiniteFiberDescent318
public import CompletedCharacterProper318
public section
noncomputable section
namespace CompletedCharacterTargetFinite318
open AlgebraicGeometry CategoryTheory Polynomial SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterBaseComparison318
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (i:Fin 4) (L:P1⟶P1)
  (hL:JLineAtlas318.chart ℚ 1≫L=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) (affinePolynomial i)).toRingHom)≫JLineAtlas318.chart ℚ 1)
  (hQ:L≫ProjectiveJLine318.structureMap ℚ=ProjectiveJLine318.structureMap ℚ)

include hQ in
lemma target_proper:IsProper (WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L):=by
  haveI:IsProper ((WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L)≫
      ProjectiveJLine318.structureMap ℚ):=by
    rw [Category.assoc,hQ,WeierstrassXStructure318.xMap_over_base]
    exact (CompletedCharacterProper318.target_proper_integral i).1
  exact IsProper.of_comp _ (ProjectiveJLine318.structureMap ℚ)

include hL hQ in
/-- The actual target t-map is finite; no unproved target-coordinate atlas
or generic-fiber-only finiteness is used. -/
theorem target_finite:IsFinite (WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L):=by
  letI:=target_proper i L hQ
  letI:=CompletedCharacterProper318.completedMap_surjective i
  haveI:IsFinite (completedMap i≫(WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L)):=by
    rw [full_composite i L hL hQ]
    exact ContactGlobalProper318.normalization_finite units
  exact ProperFiniteFiberDescent318.finite (completedMap i) _ (completedMap i).surjective
end CompletedCharacterTargetFinite318
