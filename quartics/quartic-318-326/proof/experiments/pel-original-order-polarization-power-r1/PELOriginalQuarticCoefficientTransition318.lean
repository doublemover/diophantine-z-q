module
public import PELOriginalQuarticMixedCoefficients318
public import PELOriginalAlgebraicLineCocycle318
public section
noncomputable section
namespace PELOriginalQuarticCoefficientTransition318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalMixedRatioCover318 PELOriginalMixedPointEvaluation318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalQuarticMixedCoefficients318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalSectionMultiplication318 PELOriginalLevelPowerSections318
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma quadratic_transition_value (a b : NonemptyIndex τ hτ) (z : ComplexVectors)
    (ha : z∈domain τ hτ (opens τ hτ a)) (hb : z∈domain τ hτ (opens τ hτ b)) :
    PELOriginalOpenRegularFunction318.value τ hτ (opens τ hτ a ⊓ opens τ hτ b)
      ((LineFrameCocycle318.cocycle (quadraticSheaf τ hτ) (opens τ hτ)
        (quadraticFrame τ hτ)).transition a b).val z=
      PELOriginalLevelPowerSections318.value τ hτ 2 b.val.2 z /
        PELOriginalLevelPowerSections318.value τ hτ 2 a.val.2 z := by
  let W := opens τ hτ a ⊓ opens τ hτ b
  have hz : z∈domain τ hτ W := ⟨ha,hb⟩
  let p := point τ hτ W z hz
  have hp := point_ι τ hτ W z hz
  rw [value_at_point τ hτ W _ z p hp]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
    ((LineFrameTopScalar318.ringTop W).inv _))=_
  rw [PELOriginalAlgebraicLineCocycle318.quadratic_transition_pullback]
  let q := p≫toLeft τ hτ a.val b.val
  have hq : q≫(opens τ hτ a).ι=candidateComplexPoint τ hτ (projection (P τ) z) := by
    simpa only [q,toLeft,Category.assoc,Scheme.homOfLE_ι] using hp
  have hqC : q≫(opens τ hτ a).ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ=𝟙 _ := by
    rw [←Category.assoc,hq,PELOriginalProperComplexCandidate318.candidate_point_over]
  have hn := coordinates_nonzero τ hτ a.val q z hq
  exact quadratic_evaluation τ hτ a.val b.val.2 q hqC z hn.2 hq

/-- Whole regular coefficient compatibility for arbitrary ORIGINAL
H0(4), in the exact extracted squared-quadratic line cocycle. -/
theorem transition (s : homogeneous τ hτ 4) (a b : NonemptyIndex τ hτ) :
    (candidate τ hτ).presheaf.map (homOfLE inf_le_left).op (coefficient τ hτ a s)=
      ((LineFrameCocycle318.cocycle
        (FramedLineTensorPower318.object (quadraticSheaf τ hτ) 2) (opens τ hτ)
        (FramedLineTensorPower318.frames (quadraticSheaf τ hτ) (opens τ hτ)
          (quadraticFrame τ hτ) 2)).transition a b).val *
      (candidate τ hτ).presheaf.map (homOfLE inf_le_right).op (coefficient τ hτ b s) := by
  rw [FramedLineTensorPower318.transition,Units.val_pow_eq_pow_val]
  let W := opens τ hτ a ⊓ opens τ hτ b
  apply PELOriginalOpenFunctionSeparation318.ext τ hτ W
  intro z hz
  rw [PELOriginalTranslationFrameValues318.value_mul τ hτ W _ _ z hz,
    value_restrict τ hτ _ W inf_le_left _ z hz,
    value_restrict τ hτ _ W inf_le_right _ z hz,
    coefficient_value τ hτ a s z hz.1,coefficient_value τ hτ b s z hz.2]
  have hpow (r : Γ(candidate τ hτ,W)) :
      PELOriginalOpenRegularFunction318.value τ hτ W (r^2) z=
        (PELOriginalOpenRegularFunction318.value τ hτ W r z)^2 := by
    rw [value_eq_evaluation τ hτ W _ z hz,value_eq_evaluation τ hτ W r z hz,map_pow]
  rw [hpow,quadratic_transition_value τ hτ a b z hz.1 hz.2]
  have ha := PELOriginalTranslationFrameValues318.theta_nonzero τ hτ a z hz.1
  have hb := PELOriginalTranslationFrameValues318.theta_nonzero τ hτ b z hz.2
  field_simp [ha.2,hb.2]
end PELOriginalQuarticCoefficientTransition318
