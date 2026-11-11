module
public import PELOriginalHyperplaneLocalGenerator318
public import OpenModuleBaseChangeGenerators318
public import RestrictedFreeScalarRow318
public section
noncomputable section
namespace PELOriginalHyperplaneChartFrames318
open AlgebraicGeometry CategoryTheory
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalChartOverlapLocalization318
open PELOriginalChartOverlapMorphism318 PELOriginalAlgebraicHyperplaneImage318
open PELOriginalOverlapRatioUnits318 PELOriginalHyperplaneLocalGenerator318
open GlobalScalarSheafEndomorphism318 IntegralOpenUnitMonomorphism318
variable (τ : ℂ) (hτ : 0 < τ.im) (j k : Label 3)

/-- Every literal original generator has the precise k-chart coefficient,
as an equality of whole module-sheaf morphisms. -/
theorem generator_coefficient (i : Label 3) :
    (Scheme.Modules.restrictFunctor (chartMap τ hτ k)).map
      (ChartGeneratedImageSheaf318.generator (chartMap τ hτ j) (ratios τ hτ j) i) =
    (Scheme.Modules.restrictUnitIso (chartMap τ hτ k)).hom ≫
      endomorphism _ (ratios τ hτ k i) ≫ generator τ hτ j k := by
  apply (cancel_epi (Scheme.Modules.restrictUnitIso (chartMap τ hτ k)).inv).1
  apply (cancel_mono (ambientIso τ hτ j k).hom).1
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  have hg := OpenModuleBaseChangeGenerators318.generator_square
    (right τ hτ j k) (left τ hτ j k) (chartMap τ hτ k) (chartMap τ hτ j)
    (cartesian τ hτ j k) (ratios τ hτ j) i
  rw [PELOriginalHyperplaneLocalGenerator318.generator]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  rw [show (ambientIso τ hτ j k).hom =
    (OpenModuleBaseChangeUnit318.unitIso (right τ hτ j k) (left τ hτ j k)
      (chartMap τ hτ k) (chartMap τ hτ j) (cartesian τ hτ j k)).hom from rfl]
  rw [hg]
  change _ = endomorphism _ (ratios τ hτ k i) ≫
    unitMap (right τ hτ j k) ≫
      (Scheme.Modules.pushforward (right τ hτ j k)).map (transitionIso τ hτ j k).hom
  rw [OpenScalarSheafNaturality318.unit_scalar_square,Category.assoc,
    ←Functor.map_comp,transitionIso_hom,endomorphism_comp,←section_transition]

/-- Whole restricted presentation, with no generator-only conclusion. -/
theorem presentation_factorization :
    RestrictedFreeScalarRow318.row (chartMap τ hτ k) (ratios τ hτ k) ≫
      generator τ hτ j k =
    (Scheme.Modules.restrictFunctor (chartMap τ hτ k)).map
      (ChartGeneratedImageSheaf318.presentation (chartMap τ hτ j) (ratios τ hτ j)) := by
  apply RestrictedFreeScalarRow318.factorization
  intro i
  rw [ChartGeneratedImageSheaf318.generator_presentation]
  exact generator_coefficient τ hτ j k i

/-- A produced structure-sheaf frame of the SAME global algebraic image
sheaf on EVERY original candidate chart. The row is split by k/k=1 and
the generator is a genuine mono on the entire chart. -/
@[expose] def frame :
    SheafOfModules.unit (Spec (CommRingCat.of (CoordinateChart τ hτ k))).ringCatSheaf ≅
      (Scheme.Modules.restrictFunctor (chartMap τ hτ k)).obj (imageSheaf τ hτ j) := by
  letI : Epi (RestrictedFreeScalarRow318.row (chartMap τ hτ k) (ratios τ hτ k)) :=
    RestrictedFreeScalarRow318.row_epi _ _ k (ratios_self τ hτ k)
  exact LocallyPrincipalImageFrame318.frame (chartMap τ hτ k)
    (ChartGeneratedImageSheaf318.presentation (chartMap τ hτ j) (ratios τ hτ j))
    (RestrictedFreeScalarRow318.row (chartMap τ hτ k) (ratios τ hτ k))
    (generator τ hτ j k) (presentation_factorization τ hτ j k)

@[reassoc] theorem frame_inclusion :
    (frame τ hτ j k).hom ≫ (Scheme.Modules.restrictFunctor (chartMap τ hτ k)).map
      (CategoryTheory.Limits.image.ι
        (ChartGeneratedImageSheaf318.presentation (chartMap τ hτ j) (ratios τ hτ j))) =
    generator τ hτ j k :=
  LocallyPrincipalImageFrame318.frame_inclusion _ _ _ _ _

/-- Every member of the genuine nine-chart cover has rank exactly one
for the actual global image sheaf, including the anchor-chart boundary. -/
theorem every_chart_frame : ∀ k : Label 3,
    Nonempty (SheafOfModules.unit
      (Spec (CommRingCat.of (CoordinateChart τ hτ k))).ringCatSheaf ≅
      (Scheme.Modules.restrictFunctor (chartMap τ hτ k)).obj (imageSheaf τ hτ j)) :=
  fun k => ⟨frame τ hτ j k⟩
end PELOriginalHyperplaneChartFrames318
