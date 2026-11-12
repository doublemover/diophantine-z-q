module
public import ActualTwoDescentOriginalRootNormalizedOrders318
public import ActualTwoDescentOriginalCubicChartCover318
public import Mathlib.AlgebraicGeometry.Stalk
public section
noncomputable section
namespace ActualTwoDescentOpenAffineStalkRebuild318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j] (p : PrimeSpectrum R)

/-- The actual open-immersion stalk map, followed by the native Spec
localization isomorphism. No global integrality premise is required. -/
def equivalence : X.presheaf.stalk (j p) ≃+* Localization.AtPrime p.asIdeal :=
  (asIso (j.stalkMap p) ≪≫ Spec.stalkIso (CommRingCat.of R) p).commRingCatIsoToRingEquiv

/-- The coefficient is transported along the specified native stalk
isomorphism, not an arbitrarily chosen local-ring isomorphism. -/
def coefficient (r : R) : X.presheaf.stalk (j p) :=
  (equivalence j p).symm (algebraMap R (Localization.AtPrime p.asIdeal) r)

lemma coefficient_image (r : R) :
    equivalence j p (coefficient j p r) =
      algebraMap R (Localization.AtPrime p.asIdeal) r :=
  (equivalence j p).apply_symm_apply _

instance stalkDomain [IsDomain (Localization.AtPrime p.asIdeal)] :
    IsDomain (X.presheaf.stalk (j p)) :=
  Function.Injective.isDomain (equivalence j p) (equivalence j p).injective

instance stalkDVR [IsDomain (Localization.AtPrime p.asIdeal)]
    [IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)] :
    IsDiscreteValuationRing (X.presheaf.stalk (j p)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (equivalence j p).symm
end ActualTwoDescentOpenAffineStalkRebuild318
