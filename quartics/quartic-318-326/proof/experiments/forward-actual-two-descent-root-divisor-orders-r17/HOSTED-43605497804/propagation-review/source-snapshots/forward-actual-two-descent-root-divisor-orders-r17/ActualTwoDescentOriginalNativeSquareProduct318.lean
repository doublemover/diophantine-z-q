module
public import ActualTwoDescentOriginalAffineInclusionFrame318
public section
noncomputable section
namespace ActualTwoDescentOriginalNativeSquareProduct318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentRootCofactorData318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentRootLocalizedIdeals318
open ActualTwoDescentRootLocalizedModuleFrames318 ActualTwoDescentRootLocalTensorSquare318
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalGlobalRootAffineFrames318 ActualTwoDescentOriginalRootNativeSquareCharts318
open ActualTwoDescentOriginalAffineInclusionFrame318
universe u
variable {K : Type u} [Field K] [CharZero K]

def localRegularFunction (n : K) (i : Fin 3) (b : Bool)
    (U : (Spec (CommRingCat.of (RootChartRing n i b))).Opens) : RootChartRing n i b →+* Γ(Spec (CommRingCat.of (RootChartRing n i b)),U) :=
  ((Spec (CommRingCat.of (RootChartRing n i b))).presheaf.map
    (CategoryTheory.homOfLE (show U≤⊤ from le_top)).op).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (RootChartRing n i b))).inv.hom

/-- Every subopen,including opens containing the root: multiplying the
EXACT scaled native tensor-square chart by the original root function is
literal multiplication of the SAME original ideal inclusions. -/
lemma actual_affine_square_product (n : K) (i : Fin 3) (b : Bool)
    (U : (Spec (CommRingCat.of (RootChartRing n i b))).Opens)
    (s t : Γ(originalRootIdealSheaf n i,(rootLocalizationMorphism n i b ≫ affineChart n) ''ᵁ U)) :
    localRegularFunction n i b U (rootChartMap n i b (rootNumerator n i))*
      (affineSquareChart n i b).hom.app U
        (IntrinsicTensorSheaf318.pure _ _ ((rootLocalizationMorphism n i b ≫ affineChart n) ''ᵁ U) s t)=
    (affineValue n i b).app U s*(affineValue n i b).app U t := by
  rw [actual_affine_square_pure,actual_affine_value_apply,actual_affine_value_apply]
  change localRegularFunction n i b U (rootChartMap n i b (rootNumerator n i))*
    (((originalGlobalAffineFrame n i b).hom.app U s*(originalGlobalAffineFrame n i b).hom.app U t)*
      localRegularFunction n i b U (rootSquareUnit n i b : RootChartRing n i b))=
    ((originalGlobalAffineFrame n i b).hom.app U s*localRegularFunction n i b U (rootLocalGenerator n i b))*
    ((originalGlobalAffineFrame n i b).hom.app U t*localRegularFunction n i b U (rootLocalGenerator n i b))
  have h := congrArg (localRegularFunction n i b U) (actual_root_generator_square n i b)
  rw [map_pow,map_mul] at h
  linear_combination -(originalGlobalAffineFrame n i b).hom.app U s*
    (originalGlobalAffineFrame n i b).hom.app U t*h
end ActualTwoDescentOriginalNativeSquareProduct318
