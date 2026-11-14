module
public import AffineTildePushforward318
public import IntegralNormalizationFiniteMap318
public import IntegralNormalizationCounitSheaf318
public section
noncomputable section
namespace IntegralNormalizationDualPushforward318
open AlgebraicGeometry CategoryTheory Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "A" => Source R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "into" => IntegralFourRootNormalizationConductor318.intoNormal R a d
local notation "φ" => CommRingCat.ofHom into.toRingHom
local notation "ν" => IntegralNormalizationFiniteMap318.map R a d
local notation "I" => IntegralNormalizationConductorIdeal318.ideal R a d

/-- The whole finite-dual sheaf on the ACTUAL normal-order chart. -/
@[expose] def normalDual :=
  tilde (R:=CommRingCat.of N) (ModuleCat.of N (FiniteDualModuleAction318.Dual P N))

/-- Native scheme-module pushforward along the actual finite
normalization map, not merely a renamed restricted module. -/
@[expose] def pushed := (Scheme.Modules.pushforward ν).obj (normalDual R a d)

@[expose] def restrictedIso :
    letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
    tilde (R:=CommRingCat.of A) (ModuleCat.of A (FiniteDualModuleAction318.Dual P N)) ≅
      pushed R a d := by
  letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
  exact AffineTildePushforward318.iso φ (ModuleCat.of N (FiniteDualModuleAction318.Dual P N))

/-- The actual native pushforward, not only a proxy, equals the
conductor subsheaf in raw coefficient coordinates. -/
@[expose] def conductorIso : pushed R a d ≅
    tilde (R:=CommRingCat.of A) (ModuleCat.of A I) := by
  letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
  exact (restrictedIso R a d).symm ≪≫
    IntegralNormalizationCounitSheaf318.conductorSheafIso R a d hd

/-- Actual finite-normalization counit into the raw finite-dual sheaf,
using canonical full restriction, BEFORE choosing raw coefficients. -/
@[expose] def counit : pushed R a d ⟶
    tilde (R:=CommRingCat.of A) (ModuleCat.of A (FiniteDualModuleAction318.Dual P A)) := by
  letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
  exact (restrictedIso R a d).inv ≫ (tilde.functor (CommRingCat.of A)).map
    (ModuleCat.ofHom (FiniteDualRestriction318.restriction into))

@[expose] def coefficientCounit : pushed R a d ⟶
    tilde (R:=CommRingCat.of A) (ModuleCat.of A A) := by
  letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
  exact (restrictedIso R a d).inv ≫ IntegralNormalizationCounitSheaf318.counitSheaf R a d

/-- Full native sheaf factorization into the actual conductor. -/
theorem conductor_factorization : (conductorIso R a d hd).hom ≫
    (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom I.subtype)=
      coefficientCounit R a d := by
  letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
  change ((restrictedIso R a d).inv ≫
    (IntegralNormalizationCounitSheaf318.conductorSheafIso R a d hd).hom) ≫ _=_
  rw [Category.assoc,IntegralNormalizationCounitSheaf318.counit_factorization]
  rfl

/-- Choosing the original raw coefficient frame recovers exactly the
canonical finite-dual counit; this verifies the entire map, not ranks. -/
theorem frame_counit : coefficientCounit R a d ≫
    (tilde.functor (CommRingCat.of A)).map
      (FiniteDualModuleAction318.frame P A (IntegralNormalizationCounit318.rawFrame R a d)).toModuleIso.hom=
        counit R a d := by
  letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
  change ((restrictedIso R a d).inv ≫ (tilde.functor (CommRingCat.of A)).map
    (ModuleCat.ofHom (IntegralNormalizationCounit318.coordinate R a d))) ≫ _=_
  rw [Category.assoc,←Functor.map_comp]
  congr 1
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact FiniteDualRestriction318.frame_coordinate into
    (IntegralNormalizationCounit318.rawFrame R a d) f
end IntegralNormalizationDualPushforward318
