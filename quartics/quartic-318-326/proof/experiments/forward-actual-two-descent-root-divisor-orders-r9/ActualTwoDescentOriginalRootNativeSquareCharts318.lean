module
public import ActualTwoDescentScaledNativeTensorSquareFrame318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootNativeSquareCharts318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalGlobalRootAffineFrames318 ActualTwoDescentOriginalIdealInfinityFrame318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentRootLocalTensorSquare318
open ActualTwoDescentOriginalRootIdealRestrictionComparison318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentOriginalGlobalInfinityPoleUnit318
open ActualTwoDescentScaledNativeTensorSquareFrame318
universe u
variable {K : Type u} [Field K] [CharZero K]

def affineSquareCoefficient (n : K) (i : Fin 3) (b : Bool) :
    Γ(Spec (CommRingCat.of (RootChartRing n i b)),⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (RootChartRing n i b))).inv (rootSquareUnit n i b)
lemma affineSquareCoefficient_unit (n : K) (i : Fin 3) (b : Bool) :
    IsUnit (affineSquareCoefficient n i b) :=
  (rootSquareUnit n i b).isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (RootChartRing n i b))).inv.hom

def infinitySquareCoefficient (n : K) (i : Fin 3) : Γ(infinityScheme n,⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (InfinityChart n))).inv ((rootPoleUnit n i)⁻¹)
lemma infinitySquareCoefficient_unit (n : K) (i : Fin 3) : IsUnit (infinitySquareCoefficient n i) :=
  ((rootPoleUnit n i)⁻¹).isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (InfinityChart n))).inv.hom

/-- Native tensor-square maps with the exact algebraic factors
already produced from g²=(x-a)*unit on both principal affine charts. -/
def affineSquareChart (n : K) (i : Fin 3) (b : Bool) :
    (IntrinsicTensorSheaf318.tensor (originalRootIdealSheaf n i) (originalRootIdealSheaf n i)).restrict
      (rootLocalizationMorphism n i b ≫ affineChart n) ≅
        SheafOfModules.unit (Spec (CommRingCat.of (RootChartRing n i b))).ringCatSheaf :=
  scaledSquareFrame _ _ (originalGlobalAffineFrame n i b)
    (affineSquareCoefficient n i b) (affineSquareCoefficient_unit n i b)

lemma actual_affine_square_pure (n : K) (i : Fin 3) (b : Bool)
    (U : (Spec (CommRingCat.of (RootChartRing n i b))).Opens)
    (s t : Γ(originalRootIdealSheaf n i,(rootLocalizationMorphism n i b ≫ affineChart n) ''ᵁ U)) :
    (affineSquareChart n i b).hom.app U
      (IntrinsicTensorSheaf318.pure _ _ ((rootLocalizationMorphism n i b ≫ affineChart n) ''ᵁ U) s t)=
    ((originalGlobalAffineFrame n i b).hom.app U s*(originalGlobalAffineFrame n i b).hom.app U t)*
      ((Spec (CommRingCat.of (RootChartRing n i b))).presheaf.map
        (CategoryTheory.homOfLE (show U≤⊤ from le_top)).op (affineSquareCoefficient n i b)) :=
  scaledSquareFrame_pure _ _ _ _ _ U s t

/-- Infinity uses the INVERSE of the actual pole unit because the
matching section is b/u and (x-a)*u²=poleUnit. This is not its inverse sign. -/
def infinitySquareChart (n : K) (i : Fin 3) :
    (IntrinsicTensorSheaf318.tensor (originalRootIdealSheaf n i) (originalRootIdealSheaf n i)).restrict
      (infinityChart n) ≅ SheafOfModules.unit (infinityScheme n).ringCatSheaf :=
  scaledSquareFrame _ _ (originalInfinityFrame n i)
    (infinitySquareCoefficient n i) (infinitySquareCoefficient_unit n i)

lemma actual_infinity_square_pure (n : K) (i : Fin 3) (U : (infinityScheme n).Opens)
    (s t : Γ(originalRootIdealSheaf n i,(infinityChart n) ''ᵁ U)) :
    (infinitySquareChart n i).hom.app U
      (IntrinsicTensorSheaf318.pure _ _ ((infinityChart n) ''ᵁ U) s t)=
    ((originalInfinityFrame n i).hom.app U s*(originalInfinityFrame n i).hom.app U t)*
      ((infinityScheme n).presheaf.map (CategoryTheory.homOfLE (show U≤⊤ from le_top)).op
        (infinitySquareCoefficient n i)) :=
  scaledSquareFrame_pure _ _ _ _ _ U s t
end ActualTwoDescentOriginalRootNativeSquareCharts318
