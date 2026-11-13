module
public import IntegralClosureDualNativePullback318
public import IntegralNormalFiniteDualOrder318
public import IntegralNormalTraceSheafDuality318
public section
noncomputable section
namespace IntegralNormalFiniteDualSheafRestriction318
open Polynomial IntegralDistinctContactOpen318 IntegralOriginalNormalOverlap318
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "S" => LaurentCoordinateInversion318.Base R
local notation "B" => OpenOrder R a d
local instance : Algebra S B := OriginalNormalOverlapOrderLocalization318.finiteAlgebra R a d
local instance : IsScalarTower P S B := IsScalarTower.of_algebraMap_eq
  (fun q => (finite_polynomial R a d q).symm)
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "O" => FiniteOverlap R a d
@[expose] def map := Spec.map (CommRingCat.ofHom
  (OriginalNormalOverlapOrderLocalization318.finiteInclusion R a d))
instance map_open : IsOpenImmersion (map R a d) :=
  IntegralClosureDualNativePullback318.isOpen (Q:=S) (B:=B) (X:P)

@[expose] def overlapDual : (Spec (CommRingCat.of O)).Modules :=
  tilde (R:=CommRingCat.of O) (ModuleCat.of O (FiniteDualModuleAction318.Dual S O))

/-- Full native finite-chart open restriction to the complete integral overlap dual.
This is a restriction along the actual normal-order inclusion. -/
@[expose] def restrictionIso :
    (Scheme.Modules.restrictFunctor (map R a d)).obj
      (tilde (R:=CommRingCat.of N) (ModuleCat.of N (FiniteDualModuleAction318.Dual P N))) ≅
        overlapDual R a d := by
  letI := NormalOverlapFinitePresentation318.finite_presentation R a d hd
  exact IntegralClosureDualNativePullback318.restrictionIso (Q:=S) (B:=B) (X:P)

@[expose] def pullbackIso :
    (Scheme.Modules.pullback (map R a d)).obj
      (tilde (R:=CommRingCat.of N) (ModuleCat.of N (FiniteDualModuleAction318.Dual P N))) ≅
        overlapDual R a d := by
  letI := NormalOverlapFinitePresentation318.finite_presentation R a d hd
  exact IntegralClosureDualNativePullback318.iso (Q:=S) (B:=B) (X:P)
/-- The OLD literal trace-codifferent sheaf is consumed through its
existing full finite-dual equivalence, not replaced by an abstract line. -/
@[expose] def traceRestrictionIso :
    (Scheme.Modules.restrictFunctor (map R a d)).obj
      (IntegralNormalTraceSheafDuality318.traceSheaf R a d) ≅ overlapDual R a d :=
  (Scheme.Modules.restrictFunctor (map R a d)).mapIso
    (IntegralNormalTraceSheafDuality318.traceSheafIso R a d hd) ≪≫
  restrictionIso R a d hd
end IntegralNormalFiniteDualSheafRestriction318
