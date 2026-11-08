module
public import CompletedCharacterTargetFinite318
public import ProjectiveAffineCharts318
public section
noncomputable section
namespace CompletedCharacterFinite318
open AlgebraicGeometry CategoryTheory Polynomial SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318 CompletedCharacterBaseComparison318
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal projective affine transformation undoing the published
x scaling and centroid translation, on the actual projective line. -/
@[expose] def affineTransform (i:Fin 4):P1⟶P1:=
  ProjectiveAffineLine318.map ℚ (slope i) (centroid i)
lemma affineTransform_chart (i:Fin 4):JLineAtlas318.chart ℚ 1≫affineTransform i=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) (affinePolynomial i)).toRingHom)≫JLineAtlas318.chart ℚ 1:=
  ProjectiveAffineCharts318.chart_naturality ℚ (slope i) (centroid i)
lemma affineTransform_over_Q (i:Fin 4):affineTransform i≫ProjectiveJLine318.structureMap ℚ=
    ProjectiveJLine318.structureMap ℚ:=ProjectiveAffineCharts318.map_over_base ℚ (slope i) (centroid i)

/-- Actual completed-target map to the original contact t-line, with every
published rational scaling and translation retained. -/
@[expose] def targetTMap (i:Fin 4):Target i⟶P1:=
  WeierstrassXProjection318.xMap (publishedA i) (publishedB i)≫affineTransform i

theorem targetTMap_over_Q (i:Fin 4):targetTMap i≫ProjectiveJLine318.structureMap ℚ=
    WeierstrassGluing318.structureMap (publishedA i) (publishedB i):=by
  rw [targetTMap,Category.assoc,affineTransform_over_Q,WeierstrassXStructure318.xMap_over_base]

theorem completedMap_over_t (i:Fin 4):completedMap i≫targetTMap i=
    ContactProjectiveModel318.modelMap units:=
  full_composite i (affineTransform i) (affineTransform_chart i) (affineTransform_over_Q i)

/-- The already constructed completed character map is genuinely finite. -/
theorem completedMap_finite (i:Fin 4):IsFinite (completedMap i):=
  finite_of_affine_transformation i (affineTransform i) (affineTransform_chart i) (affineTransform_over_Q i)

/-- The actual completed target is finite over the original contact t-line. -/
theorem targetTMap_finite (i:Fin 4):IsFinite (targetTMap i):=
  CompletedCharacterTargetFinite318.target_finite i (affineTransform i)
    (affineTransform_chart i) (affineTransform_over_Q i)

theorem finite_surjective (i:Fin 4):IsFinite (completedMap i)∧Surjective (completedMap i):=
  ⟨completedMap_finite i,CompletedCharacterProper318.completedMap_surjective i⟩
end CompletedCharacterFinite318
