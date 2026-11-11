module
public import PELOriginalHyperplaneChartFrames318
public section
noncomputable section
namespace PELOriginalHyperplaneSectionCoordinates318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalAlgebraicHyperplaneImage318
open PELOriginalHyperplaneChartFrames318
open GlobalScalarSheafEndomorphism318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- The nine actual global module-sheaf sections obtained from the image
factorization of the literal cubic coordinate presentation. -/
@[expose] def section (i : Label 3) :
    SheafOfModules.unit (PELOriginalReducedProjectiveCandidate318.candidate τ hτ).ringCatSheaf ⟶
      imageSheaf τ hτ j :=
  SheafOfModules.ιFree i ≫ factorThruImage
    (ChartGeneratedImageSheaf318.presentation (chartMap τ hτ j) (ratios τ hτ j))

/-- Full sheaf identity for the coefficient of EVERY global cubic
section in EVERY actual chart frame. This identifies the algebraic
atlas with the literal original hyperplane coordinate ratios. -/
theorem section_in_frame (k i : Label 3) :
    (Scheme.Modules.restrictFunctor (chartMap τ hτ k)).map (section τ hτ j i) =
      (Scheme.Modules.restrictUnitIso (chartMap τ hτ k)).hom ≫
        endomorphism _ (ratios τ hτ k i) ≫ (frame τ hτ j k).hom := by
  apply (cancel_mono ((Scheme.Modules.restrictFunctor (chartMap τ hτ k)).map
    (image.ι (ChartGeneratedImageSheaf318.presentation (chartMap τ hτ j) (ratios τ hτ j))))).1
  rw [Category.assoc,Category.assoc,frame_inclusion]
  rw [←Functor.map_comp,section,Category.assoc,image.fac,
    ChartGeneratedImageSheaf318.generator_presentation]
  exact generator_coefficient τ hτ j k i

/-- In its own chart, the kth literal cubic section is exactly the
produced frame generator, with coefficient one, not an unspecified unit. -/
theorem own_section (k : Label 3) :
    (Scheme.Modules.restrictUnitIso (chartMap τ hτ k)).inv ≫
      (Scheme.Modules.restrictFunctor (chartMap τ hτ k)).map (section τ hτ j k) =
        (frame τ hτ j k).hom := by
  rw [section_in_frame,ratios_self,endomorphism_one,Category.id_comp,
    Iso.inv_hom_id_assoc]

/-- Canonical algebraic transition identity. On the actual i/k principal
intersection the coefficient is a proved unit, so these are the actual
O(1) frame transitions, not merely relations between point values. -/
theorem linear_transition (k i : Label 3) :
    (Scheme.Modules.restrictUnitIso (chartMap τ hτ k)).inv ≫
      (Scheme.Modules.restrictFunctor (chartMap τ hτ k)).map (section τ hτ j i) =
    endomorphism _ (ratios τ hτ k i) ≫
      (Scheme.Modules.restrictUnitIso (chartMap τ hτ k)).inv ≫
        (Scheme.Modules.restrictFunctor (chartMap τ hτ k)).map (section τ hτ j k) := by
  rw [section_in_frame,Iso.inv_hom_id_assoc,own_section]

/-- The actual free module sheaf surjects onto this algebraic line
sheaf. This is the categorical image epimorphism, not pointwise spanning. -/
theorem globally_generated : Epi (factorThruImage
    (ChartGeneratedImageSheaf318.presentation (chartMap τ hτ j) (ratios τ hτ j))) :=
  inferInstance
end PELOriginalHyperplaneSectionCoordinates318
