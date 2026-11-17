module
public import ActualTwoDescentOriginalRootIdealRestrictionComparison318
public section
noncomputable section
namespace ActualTwoDescentOriginalGlobalRootAffineFrames318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalIdealAffineRestriction318 ActualTwoDescentOriginalRootIdealRestrictionComparison318
open ActualTwoDescentOriginalLocalizedIdealSheafFrames318 ActualTwoDescentRootPrincipalOpenCover318
variable {K : Type*} [Field K] [CharZero K]

/-- The actual global object now has ACTUAL restricted module frames
on both complete principal-open affine charts, including the root locus. -/
def originalGlobalAffineFrame (n : K) (i : Fin 3) (b : Bool) :
    (originalRootIdealSheaf n i).restrict (rootLocalizationMorphism n i b ≫ affineChart n) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (RootChartRing n i b))).ringCatSheaf :=
  (Scheme.Modules.restrictFunctorComp (rootLocalizationMorphism n i b) (affineChart n)).app
      (originalRootIdealSheaf n i) ≪≫
    (Scheme.Modules.restrictFunctor (rootLocalizationMorphism n i b)).mapIso
      (originalAffineRestrictionIso n i) ≪≫
    rootAffineIdealRestrictionIso n i b ≪≫ localizedIdealSheafFrame n i b

/-- The resulting two framed morphisms are literally the earlier
principal-open refinement, not a new collection of unrelated domains. -/
lemma actual_original_framed_chart (n : K) (hn : n≠0) (i : Fin 3) (b : Bool) :
    rootLocalizationMorphism n i b ≫ affineChart n=
      ActualTwoDescentOriginalRootRefinedCover318.refinedAffineChart n hn i b := rfl
end ActualTwoDescentOriginalGlobalRootAffineFrames318
