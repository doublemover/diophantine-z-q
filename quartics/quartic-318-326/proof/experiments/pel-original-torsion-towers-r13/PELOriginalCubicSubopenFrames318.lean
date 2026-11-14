module
public import PELOriginalAlgebraicPolarizationLine318
public import PELOriginalAlgebraicLineCocycle318
public section
noncomputable section
namespace PELOriginalCubicSubopenFrames318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalReducedProjectiveCandidate318 PELOriginalLevelTheta318
open PELOriginalProjectiveRatioInputs318 PELOriginalMixedRatioCover318
open PELOriginalAlgebraicPolarizationLine318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateIntegral : IsIntegral (candidate τ hτ) :=
  PELOriginalCandidateIntegral318.integral τ hτ
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ
abbrev anchorOpen := opens τ hτ (anchor τ hτ)
local instance anchorNonempty : Nonempty (anchorOpen τ hτ) := (anchor τ hτ).property

variable (U : (candidate τ hτ).Opens) [Nonempty U] (j : Label 3)
  (hU : U ≤ cubicOpen τ hτ j)
local instance openIntegral : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
local instance intersectionNonempty : Nonempty (anchorOpen τ hτ ⊓ U).toScheme :=
  IntegralOpenIntersection318.nonempty _ _

@[expose] def coefficient (i : Label 3) : Γ(U.toScheme,⊤) :=
  ProjectiveSubopenRatioAtlas318.ratio (inclusion τ hτ) U j hU i
abbrev intersection := anchorOpen τ hτ ⊓ U
@[expose] def toAnchor : (intersection τ hτ U).toScheme ⟶ (anchorOpen τ hτ).toScheme :=
  (candidate τ hτ).homOfLE inf_le_left
@[expose] def toOpen : (intersection τ hτ U).toScheme ⟶ U.toScheme :=
  (candidate τ hτ).homOfLE inf_le_right

theorem coefficient_transition (i : Label 3) :
    (toAnchor τ hτ U).appTop (cubic τ hτ (anchor τ hτ).val i)=
      (toOpen τ hτ U).appTop (coefficient τ hτ U j hU i)*
        (toAnchor τ hτ U).appTop (cubic τ hτ (anchor τ hτ).val j) := by
  simpa only [toAnchor,toOpen,cubic,coefficient,ProjectiveSubopenRatioAtlas318.ratio_restrict] using
    ProjectiveSubopenRatioAtlas318.transition (inclusion τ hτ)
      (PELOriginalProperComplexCandidate318.structureMap τ hτ)
      (PELOriginalProperComplexCandidate318.inclusion_over τ hτ) (cubic_point_model τ hτ)
      (intersection τ hτ U) (anchor τ hτ).val.1 j i
      (inf_le_left.trans inf_le_left) (inf_le_right.trans hU)

include hU in
theorem transition_unit :
    IsUnit ((toAnchor τ hτ U).appTop (cubic τ hτ (anchor τ hτ).val j)) := by
  simpa only [toAnchor,cubic,ProjectiveSubopenRatioAtlas318.ratio_restrict] using
    ProjectiveSubopenRatioAtlas318.transition_isUnit (inclusion τ hτ)
      (PELOriginalProperComplexCandidate318.structureMap τ hτ)
      (PELOriginalProperComplexCandidate318.inclusion_over τ hτ) (cubic_point_model τ hτ)
      (intersection τ hτ U) (anchor τ hτ).val.1 j
      (inf_le_left.trans inf_le_left) (inf_le_right.trans hU)

/-- A genuine frame of the SAME cubic image sheaf on ANY nonempty
subopen of a whole cubic coordinate chart. The quadratic coordinate
used for the rational anchor places no restriction on this source open. -/
@[expose] def frame : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
    (cubicSheaf τ hτ).restrict U.ι :=
  IntegralRatioImageFrame318.frame
    (toOpen τ hτ U) (toAnchor τ hτ U) U.ι (anchorOpen τ hτ).ι
    (IntegralOpenIntersection318.cartesian _ _)
    (cubic τ hτ (anchor τ hτ).val) (coefficient τ hτ U j hU)
    (transition_unit τ hτ U j hU).unit
    (fun i => by rw [IsUnit.unit_spec]; exact coefficient_transition τ hτ U j hU i)
    j (ProjectiveSubopenRatioAtlas318.ratio_self _ _ _ _)

theorem section_coefficient (i : Label 3) :
    (Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (cubicSection τ hτ i)=
      GlobalScalarSheafEndomorphism318.endomorphism U.toScheme (coefficient τ hτ U j hU i) ≫
        (frame τ hτ U j hU).hom :=
  IntegralRatioImageFrame318.section_in_frame _ _ _ _ _ _ _ _ _ _ _ _

/-- The distinguished original cubic section fixes the frame, rather
than leaving an unspecified unit normalization on each new open. -/
theorem distinguished_section :
    (Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (cubicSection τ hτ j)=
      (frame τ hτ U j hU).hom := by
  rw [section_coefficient,coefficient,ProjectiveSubopenRatioAtlas318.ratio_self,
    GlobalScalarSheafEndomorphism318.endomorphism_one,Category.id_comp]

local instance mixedNonempty (a : NonemptyIndex τ hτ) : Nonempty (opens τ hτ a) := a.property

/-- The earlier mixed frames are literally the same normalized frames,
not just frames with equal transition functions at complex points. -/
theorem mixed_frame (a : NonemptyIndex τ hτ) :
    frame τ hτ (opens τ hτ a) a.val.1 inf_le_left=cubicFrame τ hτ a := by
  apply Iso.ext
  rw [←distinguished_section]
  simpa only [cubic_self,GlobalScalarSheafEndomorphism318.endomorphism_one,Category.id_comp]
    using cubic_section_coefficient τ hτ a a.val.1
end PELOriginalCubicSubopenFrames318
