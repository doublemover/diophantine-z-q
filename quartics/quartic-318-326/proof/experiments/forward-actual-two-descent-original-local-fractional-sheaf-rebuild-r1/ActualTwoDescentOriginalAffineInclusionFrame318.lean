module
public import ActualTwoDescentPrincipalSheafFrameInclusion318
public section
noncomputable section
namespace ActualTwoDescentOriginalAffineInclusionFrame318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentRootLocalizedIdeals318
open ActualTwoDescentRootLocalizedModuleFrames318 ActualTwoDescentOriginalLocalizedIdealSheafFrames318
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalIdealAffineRestriction318 ActualTwoDescentOriginalRootAffineSheaf318
open ActualTwoDescentOriginalRootIdealRestrictionComparison318 ActualTwoDescentOriginalGlobalRootAffineFrames318
open ActualTwoDescentIdealInclusionRestrictionSquare318 ActualTwoDescentPrincipalSheafFrameInclusion318
universe u
variable {K : Type u} [Field K] [CharZero K]

def affineSource (n : K) (i : Fin 3) (b : Bool) :
    (originalRootIdealSheaf n i).restrict (rootLocalizationMorphism n i b ≫ affineChart n) ⟶
      (rootAffineSheaf n i).restrict (rootLocalizationMorphism n i b) :=
  (Scheme.Modules.restrictFunctorComp (rootLocalizationMorphism n i b) (affineChart n)).hom.app _ ≫
    (Scheme.Modules.restrictFunctor (rootLocalizationMorphism n i b)).map (originalAffineRestrictionIso n i).hom

/-- Actual affine value of a global ideal section: project to the SAME
original ideal,include it into O,and use the native structure restriction. -/
def affineValue (n : K) (i : Fin 3) (b : Bool) :
    (originalRootIdealSheaf n i).restrict (rootLocalizationMorphism n i b ≫ affineChart n) ⟶
      SheafOfModules.unit (Spec (CommRingCat.of (RootChartRing n i b))).ringCatSheaf :=
  affineSource n i b ≫ (Scheme.Modules.restrictFunctor (rootLocalizationMorphism n i b)).map
    (rootAffineInclusion n i) ≫ (Scheme.Modules.restrictUnitIso (rootLocalizationMorphism n i b)).hom

lemma actual_affine_value_localized (n : K) (i : Fin 3) (b : Bool) :
    affineValue n i b=affineSource n i b ≫ (rootAffineIdealRestrictionIso n i b).hom ≫
      inclusion (localizedRootIdeal n i b) := by
  have h := restriction_inclusion_square (RootChartRing n i b) (rootIdeal n i)
    (Submonoid.powers (rootChartElement n i b))
  change (rootAffineIdealRestrictionIso n i b).hom ≫ inclusion (localizedRootIdeal n i b)=
    (Scheme.Modules.restrictFunctor (rootLocalizationMorphism n i b)).map (rootAffineInclusion n i) ≫
      (Scheme.Modules.restrictUnitIso (rootLocalizationMorphism n i b)).hom at h
  unfold affineValue
  rw [←h]

/-- Exact whole-map factorization with the actual original generator. -/
lemma actual_affine_value_frame (n : K) (i : Fin 3) (b : Bool) :
    affineValue n i b=(originalGlobalAffineFrame n i b).hom ≫
      ClutchedModule318.multiply ((Scheme.ΓSpecIso (CommRingCat.of (RootChartRing n i b))).inv
        (rootLocalGenerator n i b)) := by
  rw [actual_affine_value_localized]
  rw [frame_inclusion (localizedRootIdeal n i b) (rootLocalGenerator n i b)
    (rootLocalFrame n i b) (actual_root_local_frame_value n i b)]
  simp only [originalGlobalAffineFrame,affineSource,Iso.trans_hom,Iso.app_hom,
    Functor.mapIso_hom,localizedIdealSheafFrame,frame,Category.assoc]

lemma actual_affine_value_apply (n : K) (i : Fin 3) (b : Bool)
    (U : (Spec (CommRingCat.of (RootChartRing n i b))).Opens)
    (s : Γ(originalRootIdealSheaf n i,(rootLocalizationMorphism n i b ≫ affineChart n) ''ᵁ U)) :
    (affineValue n i b).app U s=(originalGlobalAffineFrame n i b).hom.app U s*
      ((Spec (CommRingCat.of (RootChartRing n i b))).presheaf.map
        (CategoryTheory.homOfLE (show U≤⊤ from le_top)).op
          ((Scheme.ΓSpecIso (CommRingCat.of (RootChartRing n i b))).inv (rootLocalGenerator n i b))) := by
  rw [actual_affine_value_frame]
  exact ClutchedModule318.multiply_apply _ U _
end ActualTwoDescentOriginalAffineInclusionFrame318
