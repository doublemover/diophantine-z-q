module
public import ActualTwoDescentCanonicalIdealRestrictionComparison318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootRestrictionNormalization318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentRootLocalizedIdeals318
open ActualTwoDescentOriginalRootAffineSheaf318 ActualTwoDescentOriginalRootIdealRestrictionComparison318
open ActualTwoDescentCanonicalIdealLocalizationMap318 ActualTwoDescentCanonicalIdealRestrictionComparison318
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Identify the EXACT old principal-open restriction isomorphism,
including all scalar-extension choices,with the normalized new producer. -/
lemma actual_old_restriction_iso (n : K) (i : Fin 3) (b : Bool) :
    rootAffineIdealRestrictionIso n i b =
      restrictionIso (RootChartRing n i b) (Submonoid.powers (rootChartElement n i b))
        (rootIdeal n i) := rfl

lemma actual_old_restriction_hom (n : K) (i : Fin 3) (b : Bool) :
    (rootAffineIdealRestrictionIso n i b).hom=restrictionMap (RootChartRing n i b) (rootIdeal n i) :=
  restrictionIso_hom_eq (RootChartRing n i b) (Submonoid.powers (rootChartElement n i b))
    (rootIdeal n i)

/-- The adjoint is the actual old affine ideal map to the pushed
localized ideal. This closes the normalization ambiguity needed for gluing. -/
lemma actual_old_restriction_adjoint (n : K) (i : Fin 3) (b : Bool) :
    (Scheme.Modules.restrictAdjunction (rootLocalizationMorphism n i b)).homEquiv _ _
      (rootAffineIdealRestrictionIso n i b).hom=
    sheafMap (RootChartRing n i b) (rootIdeal n i) :=
  restriction_adjoint (RootChartRing n i b) (Submonoid.powers (rootChartElement n i b))
    (rootIdeal n i)
end ActualTwoDescentOriginalRootRestrictionNormalization318
