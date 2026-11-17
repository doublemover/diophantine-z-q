module
public import ActualTwoDescentOriginalRootRefinedCover318
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public section
noncomputable section
namespace ActualTwoDescentOriginalRootAffineSheaf318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentOriginalTwoChartCubicScheme318
variable {K : Type*} [Field K] [CharZero K]

/-- The actual original root ideal as a native affine O-module sheaf. -/
def rootAffineSheaf (n : K) (i : Fin 3) : (affineScheme n).Modules :=
  tilde (R:=CommRingCat.of (AffineChart n)) (ModuleCat.of (AffineChart n) (rootIdeal n i))
def rootIdealInclusion (n : K) (i : Fin 3) :
    ModuleCat.of (AffineChart n) (rootIdeal n i) ⟶ ModuleCat.of (AffineChart n) (AffineChart n) :=
  ModuleCat.ofHom (rootIdeal n i).subtype

/-- The map into the actual affine structure sheaf is induced by the
literal ideal inclusion, with the canonical tilde-self isomorphism. -/
def rootAffineInclusion (n : K) (i : Fin 3) :
    rootAffineSheaf n i ⟶ SheafOfModules.unit (affineScheme n).ringCatSheaf :=
  (tilde.functor (CommRingCat.of (AffineChart n))).map (rootIdealInclusion n i) ≫ tildeSelf.hom

lemma actual_root_affine_inclusion_normalization (n : K) (i : Fin 3) :
    (tilde.isoTop (R:=CommRingCat.of (AffineChart n))
      (ModuleCat.of (AffineChart n) (rootIdeal n i))).hom ≫
        moduleSpecΓFunctor.map (rootAffineInclusion n i)=
      rootIdealInclusion n i ≫
        (tilde.isoTop (R:=CommRingCat.of (AffineChart n))
          (ModuleCat.of (AffineChart n) (AffineChart n))).hom ≫
        moduleSpecΓFunctor.map (tildeSelf (R:=CommRingCat.of (AffineChart n))).hom := by
  have h := (tilde.toTildeΓNatIso (R:=CommRingCat.of (AffineChart n))).hom.naturality
    (rootIdealInclusion n i)
  have hh := congrArg (fun f => f ≫
    moduleSpecΓFunctor.map (tildeSelf (R:=CommRingCat.of (AffineChart n))).hom) h.symm
  simpa [rootAffineInclusion,tilde.toTildeΓNatIso,Category.assoc] using hh
end ActualTwoDescentOriginalRootAffineSheaf318
