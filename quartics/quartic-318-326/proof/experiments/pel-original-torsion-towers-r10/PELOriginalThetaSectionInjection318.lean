module
public import PELOriginalThetaLocalNonzerodivisor318
public import IntegralFramedSectionMono318
public section
noncomputable section
namespace PELOriginalThetaSectionInjection318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAlgebraicThetaSection318 PELOriginalThetaZeroScheme318
open PELOriginalAllPowerFrameCoordinates318 PELOriginalAllPowerGlobalSections318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateIntegral : IsIntegral (candidate τ hτ) := PELOriginalCandidateIntegral318.integral τ hτ

/-- Multiplication by the original theta section is an actual
monomorphism of sheaves on the whole candidate. -/
instance thetaMap_mono : Mono (thetaMap τ hτ) := by
  obtain ⟨a,ha⟩ := exists_anchor τ hτ
  let b : NonemptyIndex τ hτ := ⟨a,ha⟩
  letI : Nonempty (opens τ hτ b) := ha
  haveI : Mono (sectionMap τ hτ 1 (PELOriginalWholeHZeroDimension318.thetaVector τ hτ 1 0)) := by
    apply IntegralFramedSectionMono318.mono (Power τ hτ 1) _ (opens τ hτ b)
      (frame τ hτ 1 b) (PELOriginalThetaZeroScheme318.coefficient τ hτ b)
      (PELOriginalThetaLocalNonzerodivisor318.coefficient_nonzero τ hτ b)
    intro V hV r
    exact sectionMap_subopen τ hτ 1 _ b V hV r
  dsimp [thetaMap]
  infer_instance
end PELOriginalThetaSectionInjection318
