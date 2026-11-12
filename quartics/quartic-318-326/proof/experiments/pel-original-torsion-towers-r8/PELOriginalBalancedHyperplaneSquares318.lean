module
public import PELOriginalBalancedLineSquare318
public import PELOriginalBalancedCubicSections318
public import PELOriginalQuarticGlobalSections318
public section
noncomputable section
namespace PELOriginalBalancedHyperplaneSquares318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalMixedRatioCover318 PELOriginalMixedPointEvaluation318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalBalancedLineData318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalLevelTheta318 PELOriginalBalancedPowerSections318
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma cubic_transition_value (a b : NonemptyIndex τ hτ) (z : ComplexVectors)
    (ha : z∈domain τ hτ (opens τ hτ a)) (hb : z∈domain τ hτ (opens τ hτ b)) :
    value τ hτ (opens τ hτ a ⊓ opens τ hτ b)
      ((LineFrameCocycle318.cocycle (cubicSheaf τ hτ) (opens τ hτ)
        (cubicFrame τ hτ)).transition a b).val z=
      PELOriginalLevelPowerSections318.value τ hτ 3 b.val.1 z /
        PELOriginalLevelPowerSections318.value τ hτ 3 a.val.1 z := by
  let W := opens τ hτ a ⊓ opens τ hτ b
  have hz : z∈domain τ hτ W := ⟨ha,hb⟩
  let p := point τ hτ W z hz
  have hp := point_ι τ hτ W z hz
  rw [value_at_point τ hτ W _ z p hp]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
    ((LineFrameTopScalar318.ringTop W).inv _))=_
  rw [PELOriginalAlgebraicLineCocycle318.cubic_transition_pullback]
  let q := p≫toLeft τ hτ a.val b.val
  have hq : q≫(opens τ hτ a).ι=candidateComplexPoint τ hτ (projection (P τ) z) := by
    simpa only [q,toLeft,Category.assoc,Scheme.homOfLE_ι] using hp
  have hqC : q≫(opens τ hτ a).ι≫PELOriginalProperComplexCandidate318.structureMap τ hτ=𝟙 _ := by
    rw [←Category.assoc,hq,PELOriginalProperComplexCandidate318.candidate_point_over]
  have hn := coordinates_nonzero τ hτ a.val q z hq
  exact cubic_evaluation τ hτ a.val b.val.1 q hqC z hn.1 hq

lemma cubic_coefficient_value (a : ComplexVectors) (i j k : NonemptyIndex τ hτ)
    (z : ComplexVectors) (hz : z∈domain τ hτ (opens τ hτ k)) :
    value τ hτ (opens τ hτ k)
      (PELOriginalWholePowerMixedTransition318.originalCoefficient τ hτ 2 k
        (section τ hτ 3 a i.val.1 j.val.1)) z=
      PELOriginalLevelPowerSections318.value τ hτ 3 i.val.1 (z+a)*
      PELOriginalLevelPowerSections318.value τ hτ 3 j.val.1 (z-a)/
      (PELOriginalLevelPowerSections318.value τ hτ 3 k.val.1 z)^2 := by
  let p := point τ hτ (opens τ hτ k) z hz
  have he := point_ι τ hτ _ z hz
  have hn := coordinates_nonzero τ hτ k.val p z he
  rw [value_at_point τ hτ _ _ z p he]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
    ((LineFrameTopScalar318.ringTop (opens τ hτ k)).inv
      (PELOriginalWholePowerMixedTransition318.originalCoefficient τ hτ 2 k
        (section τ hτ 3 a i.val.1 j.val.1))))=_
  rw [PELOriginalWholePowerMixedTransition318.originalCoefficient,Iso.hom_inv_id_apply,
    PELOriginalWholePowerMixedCoefficient318.evaluation τ hτ 2 k.val _ p z hn.1 he]
  change PELOriginalPowerSectionLift318.lift τ hτ 6
    (PELOriginalWholeHZeroDimension318.asSection τ hτ 6 (section τ hτ 3 a i.val.1 j.val.1)) z / _ = _
  rw [lift_section]

/-- Every required regular coefficient and every actual frame equation
is produced from the original cubic line and whole H0(6). -/
@[expose] def cubicData : Data τ hτ where
  M := cubicSheaf τ hτ
  frame := cubicFrame τ hτ
  g i := PELOriginalLevelPowerSections318.value τ hτ 3 i.val.1
  nonzero i z hz := (PELOriginalTranslationFrameValues318.theta_nonzero τ hτ i z hz).1
  transition := cubic_transition_value τ hτ
  coefficient a i j k := PELOriginalWholePowerMixedTransition318.originalCoefficient τ hτ 2 k
    (section τ hτ 3 a i.val.1 j.val.1)
  coefficient_value a k i j z hz := cubic_coefficient_value τ hτ a i j k z hz

/-- The quadratic instance uses actual degree-six padding by theta2,
not a presumed algebraicity or normal generation of degree four. -/
@[expose] def quadraticData : Data τ hτ where
  M := quadraticSheaf τ hτ
  frame := quadraticFrame τ hτ
  g i := PELOriginalLevelPowerSections318.value τ hτ 2 i.val.2
  nonzero i z hz := (PELOriginalTranslationFrameValues318.theta_nonzero τ hτ i z hz).2
  transition := PELOriginalQuarticCoefficientTransition318.quadratic_transition_value τ hτ
  coefficient a i j k := PELOriginalQuarticMixedCoefficients318.coefficient τ hτ k
    (section τ hτ 2 a i.val.2 j.val.2)
  coefficient_value a k i j z hz := by
    rw [PELOriginalQuarticMixedCoefficients318.coefficient_value τ hτ k _ z hz,lift_section]

@[expose] def cubicSquareIso (a : ComplexVectors) :=
  PELOriginalBalancedLineSquare318.iso τ hτ (cubicData τ hτ) a
@[expose] def quadraticSquareIso (a : ComplexVectors) :=
  PELOriginalBalancedLineSquare318.iso τ hτ (quadraticData τ hτ) a
end PELOriginalBalancedHyperplaneSquares318
