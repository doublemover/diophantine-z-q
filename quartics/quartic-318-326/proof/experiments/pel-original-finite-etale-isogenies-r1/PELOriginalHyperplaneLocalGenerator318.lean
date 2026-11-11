module
public import PELOriginalOverlapRatioUnits318
public import IntegralOpenUnitMonomorphism318
public import OpenModuleCartesianBaseChange318
public section
noncomputable section
namespace PELOriginalHyperplaneLocalGenerator318
open AlgebraicGeometry CategoryTheory
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalChartOverlapLocalization318
open PELOriginalChartOverlapMorphism318 PELOriginalAlgebraicHyperplaneImage318
open PELOriginalOverlapRatioUnits318
variable (τ : ℂ) (hτ : 0 < τ.im) (j k : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) := chart_integral_domain τ hτ j
local instance otherChartDomain : IsDomain (CoordinateChart τ hτ k) := chart_integral_domain τ hτ k
local instance otherChartIntegral : IsIntegral (Spec (CommRingCat.of (CoordinateChart τ hτ k))) := by
  infer_instance
local instance overlapNonempty : Nonempty (Spec (CommRingCat.of (Overlap τ hτ j k))) := by
  infer_instance

/-- Restrict the actual anchor direct-image sheaf to another whole chart,
then identify it with the direct image from the genuine intersection. -/
@[expose] def ambientIso :
    (Scheme.Modules.restrictFunctor (chartMap τ hτ k)).obj
      (ChartGeneratedImageSheaf318.ambient (chartMap τ hτ j)) ≅
    (Scheme.Modules.pushforward (right τ hτ j k)).obj
      (SheafOfModules.unit (Spec (CommRingCat.of (Overlap τ hτ j k))).ringCatSheaf) :=
  OpenModuleCartesianBaseChange318.objectIso (right τ hτ j k) (left τ hτ j k)
      (chartMap τ hτ k) (chartMap τ hτ j) (cartesian τ hτ j k) _ ≪≫
    (Scheme.Modules.pushforward (right τ hτ j k)).mapIso
      (Scheme.Modules.restrictUnitIso (left τ hτ j k))

/-- The local k-th cubic generator is constructed from genuine regular
restriction and multiplication by the literal invertible ratio k/j on
the intersection. Its target is the actual restricted ambient sheaf. -/
@[expose] def generator :
    SheafOfModules.unit (Spec (CommRingCat.of (CoordinateChart τ hτ k))).ringCatSheaf ⟶
    (Scheme.Modules.restrictFunctor (chartMap τ hτ k)).obj
      (ChartGeneratedImageSheaf318.ambient (chartMap τ hτ j)) :=
  IntegralOpenUnitMonomorphism318.unitMap (right τ hτ j k) ≫
    ((Scheme.Modules.pushforward (right τ hτ j k)).mapIso
      (transitionIso τ hτ j k)).hom ≫ (ambientIso τ hτ j k).inv

/-- This is an actual module-sheaf monomorphism on the WHOLE k-th chart,
including points outside the anchor chart. Integrality proves the open
restriction injective; the other two factors are genuine isomorphisms. -/
instance generator_mono : Mono (generator τ hτ j k) := by
  dsimp [generator]
  infer_instance
end PELOriginalHyperplaneLocalGenerator318
