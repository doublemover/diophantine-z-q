module
public import PELOriginalMixedRatioCover318
public import PELOriginalLevelTwoCubicProducts318
public section
noncomputable section
namespace PELOriginalMixedPointEvaluation318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318 PELOriginalAllLevelProjectiveMap318
open PELOriginalCandidateAffineCharts318 PELOriginalCandidateNineChartCover318
open PELOriginalCandidateChartBase318 PELOriginalChartAnalyticEvaluation318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalMixedRatioCover318 PELOriginalProjectiveRatioInputs318
open ProjectivePreimageRegularRatios318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Actual map from a mixed chart into the unchanged original cubic
coordinate ring chart; the cubic preimage is literally that chart. -/
@[expose] def toAffine (a : Index) :
    (mixedOpen τ hτ a).toScheme ⟶ Spec (CommRingCat.of (CoordinateChart τ hτ a.1)) :=
  (candidate τ hτ).homOfLE (show mixedOpen τ hτ a ≤ candidateChart τ hτ a.1 from inf_le_left) ≫
    (actualChartIso τ hτ a.1).inv

@[reassoc] theorem toAffine_chart (a : Index) :
    toAffine τ hτ a ≫ chartMap τ hτ a.1 = (mixedOpen τ hτ a).ι := by
  simp only [toAffine,chartMap,Category.assoc,Iso.inv_hom_id_assoc,Scheme.homOfLE_ι]

@[reassoc] theorem toAffine_base (a : Index) :
    toAffine τ hτ a ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (CoordinateChart τ hτ a.1))) =
      (mixedOpen τ hτ a).ι ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ := by
  rw [←chart_over_complex_base,←Category.assoc,toAffine_chart]

lemma cubic_covering_point (z : ComplexVectors) :
    ComplexProjectiveSchemePoint318.point (fun i : Label 3 => value τ hτ 3 i z)
      (PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ z) =
      ambientPoint τ hτ (projection (P τ) z) := by
  apply ComplexProjectivePointEquality318.scheme_point_eq
  exact (original_covering_square τ hτ 1 z).symm

/-- Every true C-point of a mixed chart has one original representative
with BOTH prescribed coordinates nonzero and the full affine map fixed. -/
theorem point_representation (a : Index)
    (p : Spec (CommRingCat.of ℂ) ⟶ (mixedOpen τ hτ a).toScheme)
    (hp : p ≫ (mixedOpen τ hτ a).ι ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _) :
    ∃ z : ComplexVectors, ∃ h3 : value τ hτ 3 a.1 z≠0,
      value τ hτ 2 a.2 z≠0 ∧
      p ≫ toAffine τ hτ a = Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z a.1 h3).toRingHom) ∧
      p ≫ (mixedOpen τ hτ a).ι = candidateComplexPoint τ hτ (projection (P τ) z) := by
  obtain ⟨z,h3,he⟩ := PELOriginalFullCandidateSchemePoints318.every_affine_point τ hτ a.1
    (p ≫ toAffine τ hτ a) (by rw [Category.assoc,toAffine_base]; exact hp)
  have hpoint : p ≫ (mixedOpen τ hτ a).ι = candidateComplexPoint τ hτ (projection (P τ) z) := by
    rw [←toAffine_chart,←Category.assoc,he,PELOriginalChartSchemePointIdentity318.chart_point]
  let q := p ≫ (candidate τ hτ).homOfLE
    (show mixedOpen τ hτ a ≤ quadraticOpen τ hτ a.2 from inf_le_right)
  have hq : q ≫ (quadraticOpen τ hτ a.2).ι ≫
      PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ =
      ComplexProjectiveSchemePoint318.point (fun i : Label 2 => value τ hτ 2 i z)
        (PELOriginalLevelTwoSchemePoint318.cover_nonzero τ hτ z) := by
    dsimp [q]
    rw [Category.assoc,Scheme.homOfLE_ι_assoc,←Category.assoc,hpoint,
      PELOriginalLevelTwoSchemeMorphism318.original_point_action,
      PELOriginalLevelTwoSchemePoint318.covering_point]
  exact ⟨z,h3,point_coordinate_nonzero _ _ q _ _ hq,he,hpoint⟩

/-- Pulling an actual affine chart element to the mixed chart preserves
its literal original theta evaluation, with the ΓSpec map explicit. -/
lemma element_evaluation (a : Index) (c : CoordinateChart τ hτ a.1)
    (p : Spec (CommRingCat.of ℂ) ⟶ (mixedOpen τ hτ a).toScheme)
    (z : ComplexVectors) (h3 : value τ hτ 3 a.1 z≠0)
    (he : p ≫ toAffine τ hτ a = Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z a.1 h3).toRingHom)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (p.appTop ((toAffine τ hτ a).appTop ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ a.1))).inv c))) =
      algebraEvaluation τ hτ z a.1 h3 c := by
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    ((p ≫ toAffine τ hτ a).appTop ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ a.1))).inv c)) = _
  rw [he]
  have hc := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraEvaluation τ hτ z a.1 h3).toRingHom)) c
  rw [←hc]
  exact Iso.inv_hom_id_apply _ _

/-- Mixed-open membership forces both original covering coordinates
nonzero for ANY representative of the same actual candidate point. -/
lemma coordinates_nonzero (a : Index)
    (p : Spec (CommRingCat.of ℂ) ⟶ (mixedOpen τ hτ a).toScheme)
    (z : ComplexVectors)
    (he : p ≫ (mixedOpen τ hτ a).ι = candidateComplexPoint τ hτ (projection (P τ) z)) :
    value τ hτ 3 a.1 z≠0 ∧ value τ hτ 2 a.2 z≠0 := by
  constructor
  · let q := p ≫ (candidate τ hτ).homOfLE
      (show mixedOpen τ hτ a ≤ cubicOpen τ hτ a.1 from inf_le_left)
    apply point_coordinate_nonzero (inclusion τ hτ) a.1 q _
      (PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ z)
    dsimp [q]
    rw [Category.assoc,Scheme.homOfLE_ι_assoc,←Category.assoc,he,
      candidateComplexPoint_inclusion,cubic_covering_point]
  · let q := p ≫ (candidate τ hτ).homOfLE
      (show mixedOpen τ hτ a ≤ quadraticOpen τ hτ a.2 from inf_le_right)
    apply point_coordinate_nonzero (PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ) a.2 q _
      (PELOriginalLevelTwoSchemePoint318.cover_nonzero τ hτ z)
    dsimp [q]
    rw [Category.assoc,Scheme.homOfLE_ι_assoc,←Category.assoc,he,
      PELOriginalLevelTwoSchemeMorphism318.original_point_action,
      PELOriginalLevelTwoSchemePoint318.covering_point]

/-- Exact cubic mixed-chart ratio at an arbitrary original representative. -/
lemma cubic_evaluation (a : Index) (i : Label 3)
    (p : Spec (CommRingCat.of ℂ) ⟶ (mixedOpen τ hτ a).toScheme)
    (hp : p ≫ (mixedOpen τ hτ a).ι ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _)
    (z : ComplexVectors) (h3 : value τ hτ 3 a.1 z≠0)
    (he : p ≫ (mixedOpen τ hτ a).ι = candidateComplexPoint τ hτ (projection (P τ) z)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (cubic τ hτ a i)) =
      value τ hτ 3 i z/value τ hτ 3 a.1 z := by
  let q := p ≫ (candidate τ hτ).homOfLE
    (show mixedOpen τ hτ a ≤ cubicOpen τ hτ a.1 from inf_le_left)
  have hb : q ≫ (cubicOpen τ hτ a.1).ι ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _ := by
    simpa only [q,Category.assoc,Scheme.homOfLE_ι_assoc] using hp
  have hq : q ≫ (cubicOpen τ hτ a.1).ι ≫ inclusion τ hτ =
      ComplexProjectiveSchemePoint318.point (fun i : Label 3 => value τ hτ 3 i z)
        (PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ z) := by
    dsimp [q]
    rw [Category.assoc,Scheme.homOfLE_ι_assoc,←Category.assoc,he,
      candidateComplexPoint_inclusion,cubic_covering_point]
  exact evaluation (inclusion τ hτ) (PELOriginalProperComplexCandidate318.structureMap τ hτ)
    (PELOriginalProperComplexCandidate318.inclusion_over τ hτ) a.1 i q hb _ _ h3 hq

lemma quadratic_evaluation (a : Index) (i : Label 2)
    (p : Spec (CommRingCat.of ℂ) ⟶ (mixedOpen τ hτ a).toScheme)
    (hp : p ≫ (mixedOpen τ hτ a).ι ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _)
    (z : ComplexVectors) (h2 : value τ hτ 2 a.2 z≠0)
    (he : p ≫ (mixedOpen τ hτ a).ι = candidateComplexPoint τ hτ (projection (P τ) z)) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (quadratic τ hτ a i)) =
      value τ hτ 2 i z/value τ hτ 2 a.2 z := by
  let q := p ≫ (candidate τ hτ).homOfLE
    (show mixedOpen τ hτ a ≤ quadraticOpen τ hτ a.2 from inf_le_right)
  have hb : q ≫ (quadraticOpen τ hτ a.2).ι ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _ := by
    simpa only [q,Category.assoc,Scheme.homOfLE_ι_assoc] using hp
  have hq : q ≫ (quadraticOpen τ hτ a.2).ι ≫ PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ =
      ComplexProjectiveSchemePoint318.point (fun i : Label 2 => value τ hτ 2 i z)
        (PELOriginalLevelTwoSchemePoint318.cover_nonzero τ hτ z) := by
    dsimp [q]
    rw [Category.assoc,Scheme.homOfLE_ι_assoc,←Category.assoc,he,
      PELOriginalLevelTwoSchemeMorphism318.original_point_action,
      PELOriginalLevelTwoSchemePoint318.covering_point]
  exact evaluation (PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ)
    (PELOriginalProperComplexCandidate318.structureMap τ hτ)
    (PELOriginalLevelTwoSchemeMorphism318.over_complex τ hτ) a.2 i q hb _ _ h2 hq
end PELOriginalMixedPointEvaluation318
