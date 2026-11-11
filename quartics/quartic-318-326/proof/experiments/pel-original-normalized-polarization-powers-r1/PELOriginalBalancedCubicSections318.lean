module
public import PELOriginalBalancedPowerSections318
public import PELOriginalWholePowerGlobalSections318
public import PELOriginalAllLevelProjectiveMap318
public section
noncomputable section
namespace PELOriginalBalancedCubicSections318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalBalancedPowerSections318 PELOriginalSectionMultiplication318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalMixedRatioCover318 PELOriginalAlgebraicPolarizationLine318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Genuine global sections of the actual square of H3, obtained from
balanced opposite translates of the ORIGINAL cubic functions. -/
@[expose] def global (a : ComplexVectors) (i j : Label 3) :
    Γ(PELOriginalWholePowerGlobalSections318.power τ hτ 2,⊤) :=
  PELOriginalWholePowerGlobalSections318.global τ hτ 2 (section τ hτ 3 a i j)

@[expose] def sectionMap (a : ComplexVectors) (i j : Label 3) :
    SheafOfModules.unit (PELOriginalReducedProjectiveCandidate318.candidate τ hτ).ringCatSheaf ⟶
      PELOriginalWholePowerGlobalSections318.power τ hτ 2 :=
  PELOriginalWholePowerGlobalSections318.sectionMap τ hτ 2 (section τ hτ 3 a i j)

@[expose] def regular (a : ComplexVectors) (k i j : Label 3) : CoordinateChart τ hτ k :=
  PELOriginalWholePowerRegularization318.linear τ hτ 2 k (section τ hτ 3 a i j)

lemma regular_evaluation (a : ComplexVectors) (k i j : Label 3)
    (z : ComplexVectors) (hz : value τ hτ 3 k z≠0) :
    algebraEvaluation τ hτ z k hz (regular τ hτ a k i j)=
      value τ hτ 3 i (z+a)*value τ hτ 3 j (z-a)/(value τ hτ 3 k z)^2 := by
  rw [regular,PELOriginalWholePowerRegularization318.cover_evaluation]
  change PELOriginalPowerSectionLift318.lift τ hτ 6
    (PELOriginalWholeHZeroDimension318.asSection τ hτ 6 (section τ hτ 3 a i j)) z / _ = _
  rw [lift_section]

/-- All 81 balanced products, not a chosen branch or root, cover every
original point. Their eventual unit statements therefore see every
complex point of each genuine affine chart. -/
lemma values_nonzero (a z : ComplexVectors) :
    ∃ i j : Label 3,value τ hτ 3 i (z+a)*value τ hτ 3 j (z-a)≠0 := by
  classical
  have hp := PELOriginalAllLevelProjectiveMap318.coverVector_nonzero τ hτ 1 (z+a)
  have hm := PELOriginalAllLevelProjectiveMap318.coverVector_nonzero τ hτ 1 (z-a)
  obtain ⟨i,hi⟩ : ∃ i : Label 3,value τ hτ 3 i (z+a)≠0 := by
    by_contra! h
    exact hp (funext h)
  obtain ⟨j,hj⟩ : ∃ j : Label 3,value τ hτ 3 j (z-a)≠0 := by
    by_contra! h
    exact hm (funext h)
  exact ⟨i,j,mul_ne_zero hi hj⟩

lemma regular_nonzero (a z : ComplexVectors) (k : Label 3) (hz : value τ hτ 3 k z≠0) :
    ∃ i j : Label 3,algebraEvaluation τ hτ z k hz (regular τ hτ a k i j)≠0 := by
  obtain ⟨i,j,hij⟩ := values_nonzero τ hτ a z
  exact ⟨i,j,by rw [regular_evaluation]; exact div_ne_zero hij (pow_ne_zero _ hz)⟩

/-- Exact coefficients of the actual global section on EVERY original
subopen, not merely agreement of pointwise values on a dense locus. -/
lemma sectionMap_subopen (a : ComplexVectors) (i j : Label 3)
    (b : NonemptyIndex τ hτ) (V : (PELOriginalReducedProjectiveCandidate318.candidate τ hτ).Opens)
    (hV : V ≤ opens τ hτ b) (c : Γ(PELOriginalReducedProjectiveCandidate318.candidate τ hτ,V)) :
    (sectionMap τ hτ a i j).app V c=
      OpenLineFrameCoordinates318.frame (PELOriginalWholePowerGlobalSections318.power τ hτ 2)
        (opens τ hτ b) (PELOriginalWholePowerGlobalSections318.frame τ hτ 2 b) V hV
        (c*(PELOriginalReducedProjectiveCandidate318.candidate τ hτ).presheaf.map (homOfLE hV).op
          (PELOriginalWholePowerMixedTransition318.originalCoefficient τ hτ 2 b (section τ hτ 3 a i j))) :=
  PELOriginalWholePowerGlobalSections318.sectionMap_subopen τ hτ 2 (section τ hτ 3 a i j) b V hV c
end PELOriginalBalancedCubicSections318
