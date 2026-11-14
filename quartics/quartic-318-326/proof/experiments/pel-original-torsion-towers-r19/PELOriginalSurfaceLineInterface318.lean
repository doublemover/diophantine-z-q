module
public import PELOriginalCommutativeGroupObject318
public import PELOriginalCandidateAlgebraicDimension318
public import PELOriginalCubeClosedImmersion318
public import PELOriginalAlgebraicThetaSection318
public import PELOriginalAlgebraicLineSymmetry318
public section
noncomputable section
namespace PELOriginalSurfaceLineInterface318
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalMixedRatioCover318 PELOriginalCommutativeGroupObject318
attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory
variable (τ : ℂ) (hτ : 0<τ.im)
local instance : Module ℂ Γ(sheaf τ hτ,⊤) :=
  PELOriginalAlgebraicThetaSection318.sectionModule τ hτ

/-- A downstream interface on the OFFICIAL original group object and
its ACTUAL degree-one sheaf. Every field names an already constructed
map or sheaf. No represented dual or abstract principal-polarization
predicate is inserted into this certificate. -/
structure Certificate : Prop where
  commutative : IsCommAddMonObj (originalGroup τ hτ).X
  proper : IsProper (originalGroup τ hτ).X.hom
  smooth : Smooth (originalGroup τ hτ).X.hom
  integral : IsIntegral (originalGroup τ hτ).X.left
  connected : ConnectedSpace (originalGroup τ hτ).X.left
  dimension : topologicalKrullDim (originalGroup τ hτ).X.left=2
  cube_generates : Epi (PELOriginalCubeGeneratingSections318.presentation τ hτ)
  cube_closed : IsClosedImmersion (inclusion τ hτ)
  cube_chart : ∀ a : NonemptyIndex τ hτ,
    PELOriginalCubeClosedImmersion318.localMorphism τ hτ a=
      (opens τ hτ a).ι≫inclusion τ hτ
  symmetric : Nonempty ((Scheme.Modules.pullback
    (PELOriginalNegationLineCover318.negative τ hτ)).obj (sheaf τ hτ) ≅ sheaf τ hτ)
  hzero_one : Module.finrank ℂ Γ(sheaf τ hτ,⊤)=1
  theta_nonzero : PELOriginalAlgebraicThetaSection318.theta τ hτ≠0
  theta_spans : ∀ s : Γ(sheaf τ hτ,⊤),∃ c : ℂ,
    s=c • PELOriginalAlgebraicThetaSection318.theta τ hτ

/-- Every component is discharged by the concrete original producers,
including native algebraic dimension and the true cube-section map. -/
theorem actual : Certificate τ hτ := by
  obtain ⟨hp,hs,hi,hc,hd⟩ :=
    PELOriginalCandidateAlgebraicDimension318.geometric_surface τ hτ
  exact {
    commutative := inferInstance
    proper := hp
    smooth := hs
    integral := hi
    connected := hc
    dimension := hd
    cube_generates := inferInstance
    cube_closed := inferInstance
    cube_chart := PELOriginalCubeClosedImmersion318.localMorphism_eq τ hτ
    symmetric := ⟨PELOriginalAlgebraicLineSymmetry318.symmetry τ hτ⟩
    hzero_one := PELOriginalAlgebraicThetaSection318.dimension_one τ hτ
    theta_nonzero := PELOriginalAlgebraicThetaSection318.theta_nonzero τ hτ
    theta_spans := PELOriginalAlgebraicThetaSection318.spans τ hτ }

/-- All positive tensor powers retain the ORIGINAL complex scalar
structure and full, not selected-span, global-section dimension. -/
theorem all_power_hzero (n : ℕ) [NeZero n] :
    letI := PELOriginalAllPowerComplexSections318.sectionModule τ hτ n
    Module.finrank ℂ Γ(PELOriginalAllPowerFrameCoordinates318.Power τ hτ n,⊤)=n^2 :=
  PELOriginalAllPowerComplexSections318.dimension τ hτ n
end PELOriginalSurfaceLineInterface318
