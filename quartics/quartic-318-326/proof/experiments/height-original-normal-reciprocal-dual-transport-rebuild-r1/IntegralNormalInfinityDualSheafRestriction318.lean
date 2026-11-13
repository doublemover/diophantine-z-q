module
public import IntegralClosureDualNativePullback318
public import IntegralNormalInfinityDualOrder318
public import IntegralInfinityFiniteDual318
public section
noncomputable section
namespace IntegralNormalInfinityDualSheafRestriction318
open Polynomial IntegralDistinctContactOpen318 IntegralOriginalNormalOverlap318
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "S" => LaurentCoordinateInversion318.Base R
local notation "B" => OpenOrder R a d
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local instance : Algebra S B := OriginalNormalOverlapOrderLocalization318.infinityAlgebra R a d
local instance : IsScalarTower P S B := IsScalarTower.of_algebraMap_eq
  (fun q => (RingHom.congr_fun (infinity_polynomial R a d) q).symm)
local notation "N" => IntegralInfinityNormalConductor318.normalOrder R a d
local notation "O" => InfinityOverlap R a d
@[expose] def map := Spec.map (CommRingCat.ofHom
  (OriginalNormalOverlapOrderLocalization318.infinityInclusion R a d))
instance map_open : IsOpenImmersion (map R a d) :=
  IntegralClosureDualNativePullback318.isOpen (Q:=S) (B:=B) (X:P)

@[expose] def overlapDual : (Spec (CommRingCat.of O)).Modules :=
  tilde (R:=CommRingCat.of O) (ModuleCat.of O (FiniteDualModuleAction318.Dual S O))

/-- Full native infinity-chart open restriction to the complete integral overlap dual.
This is a restriction along the actual normal-order inclusion. -/
@[expose] def restrictionIso :
    (Scheme.Modules.restrictFunctor (map R a d)).obj
      (tilde (R:=CommRingCat.of N) (ModuleCat.of N (FiniteDualModuleAction318.Dual P N))) ≅
        overlapDual R a d := by
  letI := NormalOverlapFinitePresentation318.infinity_presentation R a d hd
  exact IntegralClosureDualNativePullback318.restrictionIso (Q:=S) (B:=B) (X:P)

@[expose] def pullbackIso :
    (Scheme.Modules.pullback (map R a d)).obj
      (tilde (R:=CommRingCat.of N) (ModuleCat.of N (FiniteDualModuleAction318.Dual P N))) ≅
        overlapDual R a d := by
  letI := NormalOverlapFinitePresentation318.infinity_presentation R a d hd
  exact IntegralClosureDualNativePullback318.iso (Q:=S) (B:=B) (X:P)
section Trace
local notation "F" => IntegralDistinctContactOpen318.Base R a d
local instance : Algebra P F := IntegralInfinityReciprocalScalar318.baseAlgebra R a d
local instance : IsScalarTower P F B := IntegralInfinityReciprocalScalar318.tower R a d
local notation "L" => NormalTraceDualModule318.lattice (F:=F) N

/-- Actual reciprocal trace lattice, with its previously proved
full infinity finite-dual identification and explicit reciprocal scalars. -/
@[expose] def traceRestrictionIso :
    (Scheme.Modules.restrictFunctor (map R a d)).obj
      (tilde (R:=CommRingCat.of N) (ModuleCat.of N L)) ≅ overlapDual R a d :=
  (Scheme.Modules.restrictFunctor (map R a d)).mapIso
    ((tilde.functor (CommRingCat.of N)).mapIso
      (IntegralInfinityFiniteDual318.equivalence R a d hd).toModuleIso) ≪≫
  restrictionIso R a d hd
end Trace
end IntegralNormalInfinityDualSheafRestriction318
