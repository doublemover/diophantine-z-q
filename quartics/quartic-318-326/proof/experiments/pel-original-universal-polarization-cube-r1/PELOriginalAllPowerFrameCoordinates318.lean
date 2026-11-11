module
public import PELOriginalAllPowerMixedCoefficients318
public import FramedGlobalSectionCoefficients318
public import FramedLineCoefficientGluing318
public section
noncomputable section
namespace PELOriginalAllPowerFrameCoordinates318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalTranslationFrameValues318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ)
abbrev Power := FramedLineTensorPower318.object (sheaf τ hτ) n
@[expose] def frame (a : NonemptyIndex τ hτ) :
    SheafOfModules.unit (opens τ hτ a).toScheme.ringCatSheaf ≅
      (Power τ hτ n).restrict (opens τ hτ a).ι :=
  FramedLineTensorPower318.frames (sheaf τ hτ) (opens τ hτ) (line τ hτ).frame n a
@[expose] def coefficient (s : Γ(Power τ hτ n,⊤)) (a : NonemptyIndex τ hτ) :
    Γ(candidate τ hτ,opens τ hτ a) :=
  FramedGlobalSectionCoefficients318.coefficient (Power τ hτ n) (opens τ hτ) (frame τ hτ n) s a

lemma transition_value (a b : NonemptyIndex τ hτ) (z : ComplexVectors)
    (ha : z∈chartDomain τ hτ a) (hb : z∈chartDomain τ hτ b) :
    value τ hτ (opens τ hτ a ⊓ opens τ hτ b)
      ((LineFrameCocycle318.cocycle (Power τ hτ n) (opens τ hτ)
        (frame τ hτ n)).transition a b).val z=(chartGauge τ hτ b z/chartGauge τ hτ a z)^n := by
  rw [frame,FramedLineTensorPower318.transition,Units.val_pow_eq_pow_val]
  rw [value_eq_evaluation τ hτ _ _ z (show z∈domain τ hτ _ from ⟨ha,hb⟩),map_pow,
    ←value_eq_evaluation τ hτ _ _ z (show z∈domain τ hτ _ from ⟨ha,hb⟩),
    PELOriginalTranslationFrameValues318.transition_value τ hτ a b z ha hb]

lemma coefficient_transition (s : Γ(Power τ hτ n,⊤)) (a b : NonemptyIndex τ hτ) :
    (candidate τ hτ).presheaf.map (homOfLE inf_le_left).op (coefficient τ hτ n s a)=
      ((LineFrameCocycle318.cocycle (Power τ hτ n) (opens τ hτ)
        (frame τ hτ n)).transition a b).val *
      (candidate τ hτ).presheaf.map (homOfLE inf_le_right).op (coefficient τ hτ n s b) :=
  FramedGlobalSectionCoefficients318.transition _ _ _ _ a b

/-- Full coefficient equality detects actual global sections by the
original sheaf condition, including all nonclosed source points. -/
lemma coefficients_injective : Function.Injective (coefficient τ hτ n) := by
  intro s t h
  let r := coefficient τ hτ n s
  have hs : s=FramedLineCoefficientGluing318.global (Power τ hτ n) (opens τ hτ)
      (frame τ hτ n) r (coefficient_transition τ hτ n s) (coversTop τ hτ) := by
    apply FramedLineCoefficientGluing318.global_unique
    intro a
    exact (OpenLineFrameCoordinates318.frame (Power τ hτ n) (opens τ hτ a)
      (frame τ hτ n a) (opens τ hτ a) le_rfl).apply_symm_apply _ |>.symm
  have ht : t=FramedLineCoefficientGluing318.global (Power τ hτ n) (opens τ hτ)
      (frame τ hτ n) r (coefficient_transition τ hτ n s) (coversTop τ hτ) := by
    apply FramedLineCoefficientGluing318.global_unique
    intro a
    change _=OpenLineFrameCoordinates318.frame (Power τ hτ n) (opens τ hτ a)
      (frame τ hτ n a) (opens τ hτ a) le_rfl (coefficient τ hτ n s a)
    rw [congrFun h a]
    exact (OpenLineFrameCoordinates318.frame (Power τ hτ n) (opens τ hτ a)
      (frame τ hτ n a) (opens τ hτ a) le_rfl).apply_symm_apply _ |>.symm
  exact hs.trans ht.symm
end PELOriginalAllPowerFrameCoordinates318
