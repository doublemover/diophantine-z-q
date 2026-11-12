module
public import PELOriginalThetaZeroScheme318
public import IntegralCompatibleCoefficients318
public import PELOriginalCandidateIntegral318
public section
noncomputable section
namespace PELOriginalThetaLocalNonzerodivisor318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalThetaZeroScheme318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateIntegral : IsIntegral (candidate τ hτ) := PELOriginalCandidateIntegral318.integral τ hτ

lemma exists_coefficient_nonzero : ∃ a : NonemptyIndex τ hτ,coefficient τ hτ a≠0 := by
  by_contra h
  push_neg at h
  let s := (PELOriginalAlgebraicThetaSection318.powerOneIso τ hτ).inv.app ⊤
    (PELOriginalAlgebraicThetaSection318.theta τ hτ)
  have hs : s=0 := by
    apply PELOriginalAllPowerFrameCoordinates318.coefficients_injective τ hτ 1
    funext a
    rw [show PELOriginalAllPowerFrameCoordinates318.coefficient τ hτ 1 s a=coefficient τ hτ a from
      actual_section_coefficient τ hτ a,h a]
    simp only [PELOriginalAllPowerFrameCoordinates318.coefficient,
      FramedGlobalSectionCoefficients318.coefficient,map_zero]
  have he := congrArg (fun x => (PELOriginalAlgebraicThetaSection318.powerOneIso τ hτ).hom.app ⊤ x) hs
  apply PELOriginalAlgebraicThetaSection318.theta_nonzero τ hτ
  simpa only [s,←ConcreteCategory.comp_apply,←Scheme.Modules.Hom.comp_app,
    Iso.inv_hom_id,Scheme.Modules.Hom.id_app,ConcreteCategory.id_apply,map_zero] using he

/-- Every local equation of the original theta section is genuinely
nonzero on the ENTIRE nonempty mixed chart. -/
theorem coefficient_nonzero (a : NonemptyIndex τ hτ) : coefficient τ hτ a≠0 :=
  IntegralCompatibleCoefficients318.all_nonzero (opens τ hτ) (coefficient τ hτ)
    (transition τ hτ) (compatible τ hτ) (intersection_nonempty τ hτ)
    (exists_coefficient_nonzero τ hτ) a

local instance openNonempty (a : NonemptyIndex τ hτ) : Nonempty (opens τ hτ a) := a.2
local instance openIntegral (a : NonemptyIndex τ hτ) : IsIntegral (opens τ hτ a).toScheme :=
  isIntegral_of_isOpenImmersion (opens τ hτ a).ι
lemma localEquation_nonzero (a : NonemptyIndex τ hτ) : localEquation τ hτ a≠0 := by
  intro h
  apply coefficient_nonzero τ hτ a
  have he := congrArg (LineFrameTopScalar318.ringTop (opens τ hτ a)).hom h
  simpa only [localEquation,PrincipalFrameZeroOverlaps318.coefficient,Iso.inv_hom_id_apply,map_zero] using he

/-- Actual multiplication by each local equation is injective in its
original global section ring. Together with the exact principal kernel
restriction, these are genuine local nonzerodivisor equations. No
smoothness or reducedness of the theta zero scheme is inferred. -/
theorem multiplication_injective (a : NonemptyIndex τ hτ) :
    Function.Injective (fun r : Γ((opens τ hτ a).toScheme,⊤) => localEquation τ hτ a*r) :=
  fun _ _ h => mul_left_cancel₀ (localEquation_nonzero τ hτ a) h
end PELOriginalThetaLocalNonzerodivisor318
