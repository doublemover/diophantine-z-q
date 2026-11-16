module
public import ActualTwoDescentOriginalRootRestrictionNormalization318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootLocalFrameCoefficient318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentRootLocalizedIdeals318
open ActualTwoDescentRootLocalizedModuleFrames318 ActualTwoDescentOriginalLocalizedIdealSheafFrames318
open ActualTwoDescentIdealLocalizationAdjoint318 ActualTwoDescentCanonicalIdealLocalizationMap318
universe u
variable {K : Type u} [Field K] [CharZero K]

def coefficient (n : K) (i : Fin 3) (b : Bool) (x : rootIdeal n i) : RootChartRing n i b :=
  (rootLocalFrame n i b).symm (idealModuleMap (RootChartRing n i b) (rootIdeal n i) x)

/-- The normalized coefficient is fixed by the LITERAL original
ideal element and actual local generator,with no unspecified field unit. -/
lemma actual_coefficient_value (n : K) (i : Fin 3) (b : Bool) (x : rootIdeal n i) :
    coefficient n i b x*rootLocalGenerator n i b=rootChartMap n i b (x:AffineChart n) := by
  have h := congrArg (fun z : localizedRootIdeal n i b => (z:RootChartRing n i b))
    ((rootLocalFrame n i b).apply_symm_apply
      (idealModuleMap (RootChartRing n i b) (rootIdeal n i) x))
  simpa only [actual_root_local_frame_value] using h

def localizedSection (n : K) (i : Fin 3) (b : Bool) (x : rootIdeal n i) :
    moduleSpecΓFunctor.obj (localizedIdealSheaf n i b) :=
  (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (rootChartMap n i b))
    (localizedIdealSheaf n i b)).hom
    ((moduleSpecΓFunctor.map (sheafMap (RootChartRing n i b) (rootIdeal n i)))
      ((tilde.isoTop (R:=CommRingCat.of (AffineChart n)) (ModuleCat.of (AffineChart n) (rootIdeal n i))).hom x))

/-- Actual affine sheaf restriction has the intended ideal element
as its exact global-section value. -/
lemma actual_localized_section (n : K) (i : Fin 3) (b : Bool) (x : rootIdeal n i) :
    localizedSection n i b x=
    (tilde.isoTop (R:=CommRingCat.of (RootChartRing n i b)) _).hom
      (idealModuleMap (RootChartRing n i b) (rootIdeal n i) x) :=
  global_image (RootChartRing n i b) (rootIdeal n i) x

/-- The ACTUAL prior local sheaf frame reads exactly the produced
coefficient;the tilde-to-structure-sheaf normalization is retained. -/
lemma actual_localized_frame_value (n : K) (i : Fin 3) (b : Bool) (x : rootIdeal n i) :
    (moduleSpecΓFunctor.map (localizedIdealSheafFrame n i b).hom) (localizedSection n i b x)=
    (moduleSpecΓFunctor.map (tildeSelf (R:=CommRingCat.of (RootChartRing n i b))).hom)
      ((tilde.isoTop (R:=CommRingCat.of (RootChartRing n i b))
        (ModuleCat.of (RootChartRing n i b) (RootChartRing n i b))).hom (coefficient n i b x)) := by
  rw [actual_localized_section]
  have h := (tilde.toTildeΓNatIso (R:=CommRingCat.of (RootChartRing n i b))).hom.naturality
    (rootLocalFrame n i b).symm.toModuleIso.hom
  have hh := congrArg (fun f => f ≫
    moduleSpecΓFunctor.map (tildeSelf (R:=CommRingCat.of (RootChartRing n i b))).hom) h.symm
  have hframe :
      (tilde.isoTop (R:=CommRingCat.of (RootChartRing n i b)) _).hom ≫
        moduleSpecΓFunctor.map (localizedIdealSheafFrame n i b).hom =
      (rootLocalFrame n i b).symm.toModuleIso.hom ≫
        (tilde.isoTop (R:=CommRingCat.of (RootChartRing n i b)) _).hom ≫
        moduleSpecΓFunctor.map (tildeSelf (R:=CommRingCat.of (RootChartRing n i b))).hom := by
    simpa [localizedIdealSheafFrame,tilde.toTildeΓNatIso,Category.assoc] using hh
  exact congrArg (fun f => f (idealModuleMap (RootChartRing n i b) (rootIdeal n i) x)) hframe
end ActualTwoDescentOriginalRootLocalFrameCoefficient318
