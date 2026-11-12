module
public import ActualTwoDescentOriginalIdealSheafUniversalProperty318
public section
noncomputable section
namespace ActualTwoDescentOriginalLocalizedIdealSheafFrames318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentRootCofactorData318 ActualTwoDescentRootPrincipalOpenCover318
open ActualTwoDescentRootLocalizedIdeals318 ActualTwoDescentRootLocalizedModuleFrames318
open ActualTwoDescentRootLocalTensorSquare318
open scoped TensorProduct
variable {K : Type*} [Field K] [CharZero K]

def localizedIdealSheaf (n : K) (i : Fin 3) (b : Bool) :
    (Spec (CommRingCat.of (RootChartRing n i b))).Modules :=
  tilde (R:=CommRingCat.of (RootChartRing n i b))
    (ModuleCat.of (RootChartRing n i b) (localizedRootIdeal n i b))

/-- The produced algebraic frames give actual sheaf isomorphisms on
the two literal principal-open schemes. Comparison with RESTRICTIONS of
the global pullback sheaf is deliberately not assumed here. -/
def localizedIdealSheafFrame (n : K) (i : Fin 3) (b : Bool) :
    localizedIdealSheaf n i b ≅
      SheafOfModules.unit (Spec (CommRingCat.of (RootChartRing n i b))).ringCatSheaf :=
  (tilde.functor (CommRingCat.of (RootChartRing n i b))).mapIso
    (rootLocalFrame n i b).symm.toModuleIso ≪≫ tildeSelf

/-- Genuine sheafification of the already constructed native algebraic
tensor-square multiplication. This is tilde(I tensor I); identification
with the monoidal sheaf tensor product is separate and not asserted. -/
def localizedTensorSquareSheafIso (n : K) (i : Fin 3) (b : Bool) :
    tilde (R:=CommRingCat.of (RootChartRing n i b))
      (ModuleCat.of (RootChartRing n i b)
        ((localizedRootIdeal n i b) ⊗[RootChartRing n i b] (localizedRootIdeal n i b))) ≅
      tilde (R:=CommRingCat.of (RootChartRing n i b))
        (ModuleCat.of (RootChartRing n i b)
          (Ideal.span {rootChartMap n i b (rootNumerator n i)} : Ideal (RootChartRing n i b))) :=
  (tilde.functor (CommRingCat.of (RootChartRing n i b))).mapIso
    (rootLocalSquareEquiv n i b).toModuleIso

/-- Exact tilde/global-section naturality preserves the constructed
multiplication map; no arbitrary choice of a sheaf isomorphism replaces it. -/
lemma actual_localized_square_sheaf_normalization (n : K) (i : Fin 3) (b : Bool) :
    (tilde.isoTop (R:=CommRingCat.of (RootChartRing n i b)) _).hom ≫
      moduleSpecΓFunctor.map (localizedTensorSquareSheafIso n i b).hom=
    (rootLocalSquareEquiv n i b).toModuleIso.hom ≫
      (tilde.isoTop (R:=CommRingCat.of (RootChartRing n i b)) _).hom := by
  exact ((tilde.toTildeΓNatIso (R:=CommRingCat.of (RootChartRing n i b))).hom.naturality
    (rootLocalSquareEquiv n i b).toModuleIso.hom).symm
end ActualTwoDescentOriginalLocalizedIdealSheafFrames318
