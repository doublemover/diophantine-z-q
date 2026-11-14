module
public import PELOriginalAlgebraicLineCocycle318
public import PELOriginalDegreeOneRatioBundle318
public section
noncomputable section
namespace PELOriginalMixedRatioEvaluation318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProperComplexCandidate318
open PELOriginalCandidateComplexPoints318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalMixedRatioCover318 PELOriginalAllLevelProjectiveMap318 PELOriginalLevelTheta318
open ProjectivePreimageRegularRatios318
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma quadratic_point (q : Base τ) :
    candidateComplexPoint τ hτ q ≫ PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ =
      ComplexProjectiveSchemePoint318.point (baseVector τ hτ 0 q)
        (PELOriginalLevelTwoSchemePoint318.base_nonzero τ hτ q) := by
  obtain ⟨z,rfl⟩ := quotient_surjective (P τ) q
  exact PELOriginalLevelTwoSchemeMorphism318.original_point_action τ hτ z

/-- Literal mixed-chart cubic ratios at a genuine original complex point.
The full regular function and both actual structure maps are retained. -/
theorem cubic_value (a : NonemptyIndex τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (opens τ hτ a).toScheme)
    (hp : p ≫ (opens τ hτ a).ι ≫ structureMap τ hτ = 𝟙 _)
    (q : Base τ) (he : p ≫ (opens τ hτ a).ι = candidateComplexPoint τ hτ q)
    (i : Label 3) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (cubic τ hτ a.val i)) =
      baseVector τ hτ 1 q i / baseVector τ hτ 1 q a.val.1 := by
  let r := p ≫ (candidate τ hτ).homOfLE
    (show opens τ hτ a ≤ sourceOpen (inclusion τ hτ) a.val.1 from inf_le_left)
  have hr : r ≫ (sourceOpen (inclusion τ hτ) a.val.1).ι = candidateComplexPoint τ hτ q := by
    simpa only [r,Category.assoc,Scheme.homOfLE_ι] using he
  have hv : r ≫ (sourceOpen (inclusion τ hτ) a.val.1).ι ≫ inclusion τ hτ =
      ComplexProjectiveSchemePoint318.point (baseVector τ hτ 1 q)
        (PELOriginalProjectiveCandidatePoints318.actual_coordinate_nonzero τ hτ q) := by
    rw [←Category.assoc,hr]
    exact candidateComplexPoint_inclusion τ hτ q
  exact evaluation (inclusion τ hτ) (structureMap τ hτ) (inclusion_over τ hτ)
    a.val.1 i r (by simpa only [r,Category.assoc,Scheme.homOfLE_ι] using hp)
    (baseVector τ hτ 1 q) _ (point_coordinate_nonzero _ _ r _ _ hv) hv

theorem quadratic_value (a : NonemptyIndex τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (opens τ hτ a).toScheme)
    (hp : p ≫ (opens τ hτ a).ι ≫ structureMap τ hτ = 𝟙 _)
    (q : Base τ) (he : p ≫ (opens τ hτ a).ι = candidateComplexPoint τ hτ q)
    (i : Label 2) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop (quadratic τ hτ a.val i)) =
      baseVector τ hτ 0 q i / baseVector τ hτ 0 q a.val.2 := by
  let f := PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ
  let r := p ≫ (candidate τ hτ).homOfLE
    (show opens τ hτ a ≤ sourceOpen f a.val.2 from inf_le_right)
  have hr : r ≫ (sourceOpen f a.val.2).ι = candidateComplexPoint τ hτ q := by
    simpa only [r,Category.assoc,Scheme.homOfLE_ι] using he
  have hv : r ≫ (sourceOpen f a.val.2).ι ≫ f =
      ComplexProjectiveSchemePoint318.point (baseVector τ hτ 0 q)
        (PELOriginalLevelTwoSchemePoint318.base_nonzero τ hτ q) := by
    rw [←Category.assoc,hr]
    exact quadratic_point τ hτ q
  exact evaluation f (structureMap τ hτ) (PELOriginalLevelTwoSchemeMorphism318.over_complex τ hτ)
    a.val.2 i r (by simpa only [r,Category.assoc,Scheme.homOfLE_ι] using hp)
    (baseVector τ hτ 0 q) _ (point_coordinate_nonzero _ _ r _ _ hv) hv

/-- The actual algebraic frame cocycle specializes to the REVERSED
analytic coordinate-change cocycle. This direction is forced by
frame_a(t*s)=frame_b(s), and prevents replacing L by its dual. -/
theorem original_transition (a b : NonemptyIndex τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (opens τ hτ a ⊓ opens τ hτ b).toScheme)
    (hp : p ≫ (opens τ hτ a ⊓ opens τ hτ b).ι ≫ structureMap τ hτ = 𝟙 _)
    (q : Base τ)
    (he : p ≫ (opens τ hτ a ⊓ opens τ hτ b).ι = candidateComplexPoint τ hτ q) :
    PELOriginalAlgebraicLineCocycle318.evaluation τ hτ a b p
      ((LineFrameCocycle318.cocycle (sheaf τ hτ) (opens τ hτ)
        (line τ hτ).frame).transition a b).val =
      PELOriginalDegreeOneRatioBundle318.transition τ hτ b.val a.val q := by
  rw [PELOriginalAlgebraicLineCocycle318.transition_evaluation]
  have hp' : (p ≫ toLeft τ hτ a.val b.val) ≫ (opens τ hτ a).ι ≫ structureMap τ hτ = 𝟙 _ := by
    simpa only [toLeft,Category.assoc,Scheme.homOfLE_ι] using hp
  have he' : (p ≫ toLeft τ hτ a.val b.val) ≫ (opens τ hτ a).ι = candidateComplexPoint τ hτ q := by
    simpa only [toLeft,Category.assoc,Scheme.homOfLE_ι] using he
  rw [cubic_value τ hτ a _ hp' q he',quadratic_value τ hτ a _ hp' q he']
  rfl
end PELOriginalMixedRatioEvaluation318
