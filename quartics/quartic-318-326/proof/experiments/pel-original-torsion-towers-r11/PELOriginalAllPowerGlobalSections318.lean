module
public import PELOriginalAllPowerFrameCoordinates318
public section
noncomputable section
namespace PELOriginalAllPowerGlobalSections318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAllPowerFrameCoordinates318 PELOriginalSectionMultiplication318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalTranslationFrameValues318 PELOriginalPowerSectionLift318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ)

/-- Genuine original H0(n) coefficients satisfy the WHOLE extracted
L^n cocycle, for every degree including zero. -/
lemma transition (s : homogeneous τ hτ n) (a b : NonemptyIndex τ hτ) :
    (candidate τ hτ).presheaf.map (homOfLE inf_le_left).op
        (PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ n a s)=
      ((LineFrameCocycle318.cocycle (Power τ hτ n) (opens τ hτ)
        (frame τ hτ n)).transition a b).val *
      (candidate τ hτ).presheaf.map (homOfLE inf_le_right).op
        (PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ n b s) := by
  apply PELOriginalOpenFunctionSeparation318.ext τ hτ (opens τ hτ a ⊓ opens τ hτ b)
  intro z hz
  rw [value_mul τ hτ _ _ _ z hz,value_restrict τ hτ _ _ inf_le_left _ z hz,
    value_restrict τ hτ _ _ inf_le_right _ z hz,
    PELOriginalAllPowerMixedCoefficients318.coefficient_value τ hτ n a s z hz.1,
    PELOriginalAllPowerMixedCoefficients318.coefficient_value τ hτ n b s z hz.2,
    PELOriginalAllPowerFrameCoordinates318.transition_value τ hτ n a b z hz.1 hz.2]
  have ha := PELOriginalMixedTranslationGauge318.gauge_nonzero τ hτ a.val z (theta_nonzero τ hτ a z hz.1)
  have hb := PELOriginalMixedTranslationGauge318.gauge_nonzero τ hτ b.val z (theta_nonzero τ hτ b z hz.2)
  rw [div_pow]
  field_simp [pow_ne_zero n ha,pow_ne_zero n hb]

@[expose] def algebraize (s : homogeneous τ hτ n) : Γ(Power τ hτ n,⊤) :=
  FramedLineCoefficientGluing318.global (Power τ hτ n) (opens τ hτ) (frame τ hτ n)
    (fun a => PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ n a s)
    (transition τ hτ n s) (coversTop τ hτ)
@[expose] def sectionMap (s : homogeneous τ hτ n) :
    SheafOfModules.unit (candidate τ hτ).ringCatSheaf ⟶ Power τ hτ n :=
  FramedLineCoefficientGluing318.sectionMap (Power τ hτ n) (opens τ hτ) (frame τ hτ n)
    (fun a => PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ n a s)
    (transition τ hτ n s) (coversTop τ hτ)

lemma coefficient_algebraize (s : homogeneous τ hτ n) (a : NonemptyIndex τ hτ) :
    coefficient τ hτ n (algebraize τ hτ n s) a=
      PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ n a s := by
  change (OpenLineFrameCoordinates318.frame (Power τ hτ n) (opens τ hτ a)
    (frame τ hτ n a) (opens τ hτ a) le_rfl).symm
      ((Power τ hτ n).presheaf.map (homOfLE le_top).op (algebraize τ hτ n s))=_
  rw [algebraize,FramedLineCoefficientGluing318.global_restrict]
  exact LinearEquiv.symm_apply_apply _ _

/-- The real section morphism on EVERY smaller open, retaining its
actual degree-one tensor-power frame and full structure-sheaf scalars. -/
theorem sectionMap_subopen (s : homogeneous τ hτ n) (a : NonemptyIndex τ hτ)
    (V : (candidate τ hτ).Opens) (hV : V≤opens τ hτ a) (c : Γ(candidate τ hτ,V)) :
    (sectionMap τ hτ n s).app V c=
      OpenLineFrameCoordinates318.frame (Power τ hτ n) (opens τ hτ a) (frame τ hτ n a) V hV
        (c*(candidate τ hτ).presheaf.map (homOfLE hV).op
          (PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ n a s)) :=
  FramedLineCoefficientGluing318.sectionMap_subopen _ _ _ _ _ _ a V hV c
end PELOriginalAllPowerGlobalSections318
