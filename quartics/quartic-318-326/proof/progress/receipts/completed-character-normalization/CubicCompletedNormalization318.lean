module
public import CubicCompletedAffine318
public section
noncomputable section
namespace CubicCompletedNormalization318
open AlgebraicGeometry CategoryTheory Polynomial SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterBaseComparison318
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (i:Fin 4) (L:P1⟶P1)
  (hL:JLineAtlas318.chart ℚ 1≫L=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) (affinePolynomial i)).toRingHom)≫JLineAtlas318.chart ℚ 1)
  (hQ:L≫ProjectiveJLine318.structureMap ℚ=ProjectiveJLine318.structureMap ℚ)

/-- The canonical map from the existing relative cubic normalization to
the actual completed Weierstrass target, supplied by the actual finite t-map. -/
@[expose] def comparison:SourceCharacterGlobal318.Model i⟶Target i:=by
  letI:=CompletedCharacterTargetFinite318.target_finite i L hL hQ
  exact (SourceCharacterGlobal318.coverMap i).normalizationDesc (CubicCompletedAffine318.embedding i)
    (WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L)
    (CubicCompletedAffine318.factor i L hL).symm

lemma on_cubic:
    (SourceCharacterGlobal318.coverMap i).toNormalization≫comparison i L hL hQ=
      CubicCompletedAffine318.embedding i:=by
  letI:=CompletedCharacterTargetFinite318.target_finite i L hL hQ
  exact (SourceCharacterGlobal318.coverMap i).toNormalization_normalizationDesc _ _ _
lemma over_line:
    comparison i L hL hQ≫(WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫L)=
      SourceCharacterGlobal318.modelMap i:=by
  letI:=CompletedCharacterTargetFinite318.target_finite i L hL hQ
  exact (SourceCharacterGlobal318.coverMap i).normalizationDesc_comp _ _ _

/-- This is an actual integral comparison morphism. Isomorphism is a
separate theorem and is not inferred from its affine restriction. -/
theorem comparison_integral:IsIntegralHom (comparison i L hL hQ):=by
  letI:=CompletedCharacterTargetFinite318.target_finite i L hL hQ
  unfold comparison
  infer_instance
end CubicCompletedNormalization318
