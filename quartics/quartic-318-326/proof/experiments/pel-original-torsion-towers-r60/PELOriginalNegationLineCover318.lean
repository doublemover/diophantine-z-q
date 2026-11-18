module
public import PELOriginalTranslationFrameValues318
public import PELOriginalNegationSchemePointAction318
public import OpenLineFrameRefinement318
public section
noncomputable section
namespace PELOriginalNegationLineCover318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalMixedRatioCover318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalProjectiveNegation318 PELOriginalOpenRegularFunction318
variable (τ : ℂ) (hτ : 0 < τ.im)
abbrev Index := NonemptyIndex τ hτ × NonemptyIndex τ hτ
abbrev negative := candidateNegation τ hτ
abbrev pullback := (Scheme.Modules.pullback (negative τ hτ)).obj (sheaf τ hτ)
@[expose] def chart (a : Index τ hτ) : (candidate τ hτ).Opens :=
  opens τ hτ a.1 ⊓ negative τ hτ ⁻¹ᵁ opens τ hτ a.2

lemma covers : (⊤ : (candidate τ hτ).Opens) ≤ ⨆ a,chart τ hτ a :=
  TranslatedLineIsoScalars318.covers (negative τ hτ) (opens τ hτ) (coversTop τ hτ)

@[expose] def sourceFrame (a : Index τ hτ) :
    SheafOfModules.unit (chart τ hτ a).toScheme.ringCatSheaf ≅
      (sheaf τ hτ).restrict (chart τ hτ a).ι :=
  OpenLineFrameRefinement318.frame (sheaf τ hτ) (opens τ hτ a.1)
    ((line τ hτ).frame a.1) (chart τ hτ a) inf_le_left
@[expose] def targetFrame (a : Index τ hτ) :
    SheafOfModules.unit (chart τ hτ a).toScheme.ringCatSheaf ≅
      (pullback τ hτ).restrict (chart τ hτ a).ι :=
  OpenLineFrameRefinement318.frame (pullback τ hτ)
    (negative τ hτ ⁻¹ᵁ opens τ hτ a.2)
    (LinePullbackFrames318.frame (negative τ hτ) (sheaf τ hτ)
      (opens τ hτ a.2) ((line τ hτ).frame a.2)) (chart τ hτ a) inf_le_right

lemma negative_point (z : ComplexVectors) :
    candidateComplexPoint τ hτ (projection (P τ) z)≫negative τ hτ=
      candidateComplexPoint τ hτ (projection (P τ) (-z)) :=
  PELOriginalNegationSchemePointAction318.original_scheme_point_action τ hτ z

lemma domain_iff (a : Index τ hτ) (z : ComplexVectors) :
    z∈domain τ hτ (chart τ hτ a) ↔
      z∈domain τ hτ (opens τ hτ a.1) ∧ -z∈domain τ hτ (opens τ hτ a.2) := by
  change (_∈opens τ hτ a.1 ∧ negative τ hτ
      (candidateComplexPoint τ hτ (projection (P τ) z) (IsLocalRing.closedPoint ℂ))∈opens τ hτ a.2) ↔ _
  rw [←Scheme.Hom.comp_apply,negative_point]
  rfl

/-- Every actual point of a symmetry chart has an original cover
representative in BOTH the original and the negated mixed chart. -/
lemma point_representation (a : Index τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (chart τ hτ a).toScheme)
    (hp : p≫(chart τ hτ a).ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ=𝟙 _) :
    ∃ z : ComplexVectors, z∈domain τ hτ (chart τ hτ a) ∧
      p≫(chart τ hτ a).ι=candidateComplexPoint τ hτ (projection (P τ) z) := by
  obtain ⟨j,z,hj,he⟩ := PELOriginalFullCandidateSchemePoints318.every_candidate_point τ hτ
    (p≫(chart τ hτ a).ι) hp
  have hz := he.trans (PELOriginalChartSchemePointIdentity318.chart_point τ hτ j z hj)
  refine ⟨z,?_,hz⟩
  change candidateComplexPoint τ hτ (projection (P τ) z) (IsLocalRing.closedPoint ℂ)∈chart τ hτ a
  rw [←hz]
  exact (p (IsLocalRing.closedPoint ℂ)).property
end PELOriginalNegationLineCover318
