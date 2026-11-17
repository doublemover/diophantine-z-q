module
public import ActualTwoDescentLocalizedIdealTensorEquivalence318
public import TildePullback318
public import ScalarExtensionTensor318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootIdealRestrictionComparison318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentRootLocalizedIdeals318
open ActualTwoDescentOriginalRootAffineSheaf318 ActualTwoDescentOriginalLocalizedIdealSheafFrames318
open ActualTwoDescentLocalizedIdealTensorEquivalence318
variable {K : Type*} [Field K] [CharZero K]

def rootLocalizationMorphism (n : K) (i : Fin 3) (b : Bool) :
    Spec (CommRingCat.of (RootChartRing n i b)) ⟶ Spec (CommRingCat.of (AffineChart n)) :=
  Spec.map (CommRingCat.ofHom (rootChartMap n i b))
instance rootLocalizationMorphism_open (n : K) (i : Fin 3) (b : Bool) :
    IsOpenImmersion (rootLocalizationMorphism n i b) :=
  IsOpenImmersion.of_isLocalization (rootChartElement n i b)

def rootIdealExtensionEquiv (n : K) (i : Fin 3) (b : Bool) :
    (ModuleCat.extendScalars (rootChartMap n i b)).obj
      (ModuleCat.of (AffineChart n) (rootIdeal n i)) ≃ₗ[RootChartRing n i b] localizedRootIdeal n i b :=
  (ScalarExtensionTensor318.tensorEquiv (S:=AffineChart n) (T:=RootChartRing n i b)
    (ModuleCat.of (AffineChart n) (rootIdeal n i))).trans
      (localizedIdealTensorEquiv (RootChartRing n i b)
        (Submonoid.powers (rootChartElement n i b)) (rootIdeal n i))

/-- Actual restriction of the original affine tilde ideal agrees with
the previously constructed local tilde ideal, via native scalar extension. -/
def rootAffineIdealRestrictionIso (n : K) (i : Fin 3) (b : Bool) :
    (rootAffineSheaf n i).restrict (rootLocalizationMorphism n i b) ≅ localizedIdealSheaf n i b :=
  (TildePullback318.restrictionIso (CommRingCat.ofHom (rootChartMap n i b))).app
      (ModuleCat.of (AffineChart n) (rootIdeal n i)) ≪≫
    (tilde.functor (CommRingCat.of (RootChartRing n i b))).mapIso
      (rootIdealExtensionEquiv n i b).toModuleIso
end ActualTwoDescentOriginalRootIdealRestrictionComparison318
