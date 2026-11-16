module
public import PELOriginalQuarticCoefficientTransition318
public import FramedLineCoefficientGluing318
public section
noncomputable section
namespace PELOriginalQuarticGlobalSections318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalSectionMultiplication318
open PELOriginalQuarticMixedCoefficients318
variable (τ : ℂ) (hτ : 0 < τ.im)
abbrev Power := FramedLineTensorPower318.object (quadraticSheaf τ hτ) 2
@[expose] def frame (a : NonemptyIndex τ hτ) :
    SheafOfModules.unit (opens τ hτ a).toScheme.ringCatSheaf ≅
      (Power τ hτ).restrict (opens τ hτ a).ι :=
  FramedLineTensorPower318.frames (quadraticSheaf τ hτ) (opens τ hτ) (quadraticFrame τ hτ) 2 a

/-- Every original degree-four holomorphic section gives an ACTUAL
global section of the genuine quadratic hyperplane sheaf squared. -/
@[expose] def global (s : homogeneous τ hτ 4) : Γ(Power τ hτ,⊤) :=
  FramedLineCoefficientGluing318.global (Power τ hτ) (opens τ hτ) (frame τ hτ)
    (fun a => coefficient τ hτ a s) (PELOriginalQuarticCoefficientTransition318.transition τ hτ s)
    (coversTop τ hτ)
@[expose] def sectionMap (s : homogeneous τ hτ 4) :
    SheafOfModules.unit (candidate τ hτ).ringCatSheaf ⟶ Power τ hτ :=
  FramedLineCoefficientGluing318.sectionMap (Power τ hτ) (opens τ hτ) (frame τ hτ)
    (fun a => coefficient τ hτ a s) (PELOriginalQuarticCoefficientTransition318.transition τ hτ s)
    (coversTop τ hτ)
lemma global_restrict (s : homogeneous τ hτ 4) (a : NonemptyIndex τ hτ) :
    (Power τ hτ).presheaf.map (homOfLE (show opens τ hτ a ≤ ⊤ from le_top)).op
      (global τ hτ s)=
    OpenLineFrameCoordinates318.frame (Power τ hτ) (opens τ hτ a)
      (frame τ hτ a) (opens τ hτ a) le_rfl (coefficient τ hτ a s) :=
  FramedLineCoefficientGluing318.global_restrict _ _ _ _ _ _ a

/-- Literal coefficient action of the genuine module-sheaf morphism
on EVERY smaller open and every original regular ring section. -/
theorem sectionMap_subopen (s : homogeneous τ hτ 4) (a : NonemptyIndex τ hτ)
    (V : (candidate τ hτ).Opens) (hV : V≤opens τ hτ a) (r : Γ(candidate τ hτ,V)) :
    (sectionMap τ hτ s).app V r=
      OpenLineFrameCoordinates318.frame (Power τ hτ) (opens τ hτ a) (frame τ hτ a) V hV
        (r*(candidate τ hτ).presheaf.map (homOfLE hV).op (coefficient τ hτ a s)) :=
  FramedLineCoefficientGluing318.sectionMap_subopen _ _ _ _ _ _ a V hV r
end PELOriginalQuarticGlobalSections318
