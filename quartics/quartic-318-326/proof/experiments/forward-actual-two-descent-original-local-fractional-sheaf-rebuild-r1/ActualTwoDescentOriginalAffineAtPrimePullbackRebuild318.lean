module
public import ActualTwoDescentLocalizedIdealNativePullbackRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalAffineAtPrimePullbackRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalIdealAffineRestriction318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentAffineChartCoordinates318
universe u
variable {K : Type u} [Field K] [CharZero K]

def localMap (n : K) (P : Ideal (AffineChart n)) [P.IsPrime] :
    Spec (CommRingCat.of (Localization.AtPrime P)) ⟶ affineScheme n :=
  Spec.map (CommRingCat.ofHom (algebraMap (AffineChart n) (Localization.AtPrime P)))
def map (n : K) (P : Ideal (AffineChart n)) [P.IsPrime] := localMap n P ≫ affineChart n

/-- Pullback of the SAME old global ideal sheaf to every actual affine
local spectrum. No localization-at-a-point open immersion is assumed. -/
def iso (n : K) (i : Fin 3) (P : Ideal (AffineChart n)) [P.IsPrime] :
    (Scheme.Modules.pullback (map n P)).obj (originalRootIdealSheaf n i) ≅
      tilde (R:=CommRingCat.of (Localization.AtPrime P))
        (ModuleCat.of (Localization.AtPrime P)
          ((rootIdeal n i).map (algebraMap (AffineChart n) (Localization.AtPrime P)))) :=
  ((Scheme.Modules.pullbackComp (localMap n P) (affineChart n)).app
      (originalRootIdealSheaf n i)).symm ≪≫
  (Scheme.Modules.pullback (localMap n P)).mapIso
    (((Scheme.Modules.restrictFunctorIsoPullback (affineChart n)).app
      (originalRootIdealSheaf n i)).symm ≪≫ originalAffineRestrictionIso n i) ≪≫
  ActualTwoDescentLocalizedIdealNativePullbackRebuild318.iso
    (Localization.AtPrime P) P.primeCompl (rootIdeal n i)

/-- Every affine prime away from Ta has the full regular ideal image. -/
theorem off_root_ideal (n : K) (i : Fin 3) (P : Ideal (AffineChart n)) [P.IsPrime]
    (hP : P ≠ rootIdeal n i) :
    (rootIdeal n i).map (algebraMap (AffineChart n) (Localization.AtPrime P))=⊤ := by
  have hx : rootNumerator n i ∈ rootIdeal n i :=
    (ActualTwoDescentOriginalRootAffineSupport318.actual_root_prime_support
      n i (rootIdeal n i)).mpr rfl
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hx)
    (ActualTwoDescentOriginalRootAffineSupport318.actual_root_unit_off_support n i P hP)

end ActualTwoDescentOriginalAffineAtPrimePullbackRebuild318
