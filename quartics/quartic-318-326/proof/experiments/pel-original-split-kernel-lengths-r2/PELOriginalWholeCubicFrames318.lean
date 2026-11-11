module
public import PELOriginalCubicSubopenFrames318
public import PELOriginalCandidateNineChartCover318
public import FramedLineTensorPower318
public import FramedGlobalSectionCoefficients318
public section
noncomputable section
namespace PELOriginalWholeCubicFrames318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalLevelTheta318
open PELOriginalCandidateAffineCharts318 PELOriginalCandidateNineChartCover318
open PELOriginalAlgebraicPolarizationLine318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance chartNonempty (j : Label 3) : Nonempty (candidateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.chart_nonempty τ hτ j

/-- Frames on all NINE WHOLE affine charts, not merely on the mixed
cubic/quadratic refinement. The object is the unchanged actual H3. -/
@[expose] def frame (j : Label 3) :
    SheafOfModules.unit (candidateChart τ hτ j).toScheme.ringCatSheaf ≅
      (cubicSheaf τ hτ).restrict (candidateChart τ hτ j).ι :=
  PELOriginalCubicSubopenFrames318.frame τ hτ (candidateChart τ hτ j) j le_rfl

lemma coversTop : (⊤ : (candidate τ hτ).Opens) ≤ ⨆ j : Label 3,candidateChart τ hτ j := by
  intro x hx
  obtain ⟨j,hj⟩ := charts_cover τ hτ x
  exact le_iSup (candidateChart τ hτ) j hj

@[expose] def powerFrame (m : ℕ) (j : Label 3) :
    SheafOfModules.unit (candidateChart τ hτ j).toScheme.ringCatSheaf ≅
      (FramedLineTensorPower318.object (cubicSheaf τ hτ) m).restrict (candidateChart τ hτ j).ι :=
  FramedLineTensorPower318.frames (cubicSheaf τ hτ) (candidateChart τ hτ) (frame τ hτ) m j

/-- The normalized whole cubic frame is fixed by its original global
cubic section on the entire chart, before evaluating at any point. -/
lemma distinguished (j : Label 3) :
    (Scheme.Modules.restrictUnitIso (candidateChart τ hτ j).ι).inv ≫
      (Scheme.Modules.restrictFunctor (candidateChart τ hτ j).ι).map (cubicSection τ hτ j)=
      (frame τ hτ j).hom :=
  PELOriginalCubicSubopenFrames318.distinguished_section τ hτ _ j le_rfl

lemma section_coefficient (j i : Label 3) :
    (Scheme.Modules.restrictUnitIso (candidateChart τ hτ j).ι).inv ≫
      (Scheme.Modules.restrictFunctor (candidateChart τ hτ j).ι).map (cubicSection τ hτ i)=
      GlobalScalarSheafEndomorphism318.endomorphism _
        (PELOriginalCubicSubopenFrames318.coefficient τ hτ (candidateChart τ hτ j) j le_rfl i) ≫
      (frame τ hτ j).hom :=
  PELOriginalCubicSubopenFrames318.section_coefficient τ hτ _ j le_rfl i

lemma transition_value (j k : Label 3) :
    ((LineFrameCocycle318.cocycle (cubicSheaf τ hτ) (candidateChart τ hτ)
      (frame τ hτ)).transition j k).val=
    GlobalSectionFrameCoordinates318.coefficient (candidateChart τ hτ j)
      (PELOriginalCubicSubopenFrames318.coefficient τ hτ (candidateChart τ hτ j) j le_rfl k)
      (candidateChart τ hτ j ⊓ candidateChart τ hτ k) inf_le_left := by
  exact GlobalSectionFrameCocycle318.transition_value _ _ _
    (cubicSection τ hτ k) j k _ (section_coefficient τ hτ j k) (distinguished τ hτ k)

/-- Coefficients of ANY genuine algebraic global power section on the
WHOLE original affine chart, in the actual original-open ring. -/
@[expose] def coefficient (m : ℕ)
    (s : Γ(FramedLineTensorPower318.object (cubicSheaf τ hτ) m,⊤)) (j : Label 3) :
    Γ(candidate τ hτ,candidateChart τ hτ j) :=
  (OpenLineFrameCoordinates318.frame (FramedLineTensorPower318.object (cubicSheaf τ hτ) m)
    (candidateChart τ hτ j) (powerFrame τ hτ m j) (candidateChart τ hτ j) le_rfl).symm
    ((FramedLineTensorPower318.object (cubicSheaf τ hτ) m).presheaf.map
      (homOfLE (show candidateChart τ hτ j ≤ ⊤ from le_top)).op s)

/-- Exact entire original coordinate-ring element recovered from that
coefficient. The chart scheme isomorphism and ΓSpec map are explicit. -/
@[expose] def element (m : ℕ)
    (s : Γ(FramedLineTensorPower318.object (cubicSheaf τ hτ) m,⊤)) (j : Label 3) :
    CoordinateChart τ hτ j :=
  (Scheme.ΓSpecIso (CommRingCat.of (CoordinateChart τ hτ j))).hom
    ((actualChartIso τ hτ j).hom.appTop
      ((LineFrameTopScalar318.ringTop (candidateChart τ hτ j)).inv (coefficient τ hτ m s j)))
/-- The full regular coefficient overlap equation for ANY global
algebraic power section, with literal extracted tensor-power units. -/
theorem coefficient_transition (m : ℕ)
    (s : Γ(FramedLineTensorPower318.object (cubicSheaf τ hτ) m,⊤)) (j k : Label 3) :
    (candidate τ hτ).presheaf.map (homOfLE
      (show candidateChart τ hτ j ⊓ candidateChart τ hτ k ≤ candidateChart τ hτ j from inf_le_left)).op
      (coefficient τ hτ m s j)=
    ((LineFrameCocycle318.cocycle (cubicSheaf τ hτ) (candidateChart τ hτ)
      (frame τ hτ)).transition j k).val^m *
    (candidate τ hτ).presheaf.map (homOfLE
      (show candidateChart τ hτ j ⊓ candidateChart τ hτ k ≤ candidateChart τ hτ k from inf_le_right)).op
      (coefficient τ hτ m s k) := by
  have h := FramedGlobalSectionCoefficients318.transition
    (FramedLineTensorPower318.object (cubicSheaf τ hτ) m)
    (candidateChart τ hτ) (powerFrame τ hτ m) s j k
  simpa only [powerFrame,FramedLineTensorPower318.transition,Units.val_pow_eq_pow_val]
    using h
end PELOriginalWholeCubicFrames318
