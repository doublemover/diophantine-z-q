module
public import AffineFiniteDualSheafAdjunction318
public import IntegralNormalizationFiniteDual318
public section
noncomputable section
namespace IntegralNormalTraceSheafDuality318
open AlgebraicGeometry CategoryTheory Polynomial IntegralDistinctContactOpen318
universe u
variable (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "B" => OpenOrder R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "L" => NormalTraceDualModule318.lattice (F:=F) N
local notation "D" => FiniteDualModuleAction318.Dual P N
local notation "E" => IntegralNormalizationFiniteDual318.equivalence R a d hd
local notation "π" => AffineFiniteDualSheafAdjunction318.projection P N

abbrev traceSheaf := tilde (R:=CommRingCat.of N) (ModuleCat.of N L)

/-- The literal trace-codifferent sheaf, not a rank-one substitute, is
the entire affine finite dual for the actual polynomial projection. -/
@[expose] def traceSheafIso : traceSheaf R a d ≅
    AffineFiniteDualSheafAdjunction318.dualSheaf P N :=
  (tilde.functor (CommRingCat.of N)).mapIso E.toModuleIso

/-- Actual affine sheaf duality with the SAME trace-codifferent on the
normal chart, for every N-module input and all native sheaf morphisms. -/
@[expose] def homEquiv (M : ModuleCat.{u} N) :
    (tilde M ⟶ traceSheaf R a d) ≃
      ((Scheme.Modules.pushforward π).obj (tilde M) ⟶
        tilde (R:=CommRingCat.of P) (ModuleCat.of P P)) :=
  (AffineTildeHomEquivalence318.postcomposeIso (traceSheafIso R a d hd)).trans
    (AffineFiniteDualSheafAdjunction318.homEquiv P N M)

/-- Its underlying counit is literally the original algebra trace of
the coefficient, tested on every input of any actual normal-order module. -/
@[expose] def moduleCounit (M : ModuleCat.{u} N) (f : M →ₗ[N] L) :
    letI : Module P M := Module.compHom M (algebraMap P N)
    letI : IsScalarTower P N M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    M →ₗ[P] P := by
  letI : Module P M := Module.compHom M (algebraMap P N)
  letI : IsScalarTower P N M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact FiniteDualAdjunction318.evaluateOne (E.toLinearMap.comp f)

theorem moduleCounit_trace (M : ModuleCat.{u} N) (f : M →ₗ[N] L) (m : M) :
    algebraMap P F (moduleCounit R a d hd M f m)=Algebra.trace F B (f m).val := by
  have h := IntegralNormalizationFiniteDual318.trace_value R a d hd (f m) 1
  change algebraMap P F (moduleCounit R a d hd M f m)=
    Algebra.trace F B ((f m).val*1) at h
  simpa only [mul_one] using h

lemma traceSheaf_coordinate (M : ModuleCat.{u} N) (f : M →ₗ[N] L) :
    AffineTildeHomEquivalence318.equivalence M (ModuleCat.of N D)
      ((tilde.functor (CommRingCat.of N)).map (ModuleCat.ofHom f) ≫
        (traceSheafIso R a d hd).hom)=E.toLinearMap.comp f := by
  change AffineTildeHomEquivalence318.equivalence M (ModuleCat.of N D)
    ((tilde.functor (CommRingCat.of N)).map (ModuleCat.ofHom f) ≫
      (tilde.functor (CommRingCat.of N)).map E.toModuleIso.hom)=_
  rw [←Functor.map_comp]
  exact AffineTildeHomEquivalence318.map_value M (ModuleCat.of N D) (E.toLinearMap.comp f)

/-- The full sheaf duality uses this literal trace counit after the
SPECIFIED native pushforward comparison. Not merely existence of some
nondegenerate pairing or abstract adjunction with untracked scalars. -/
theorem sheafCounit_formula (M : ModuleCat.{u} N) (f : M →ₗ[N] L) :
    letI : Module P M := Module.compHom M (algebraMap P N)
    letI : IsScalarTower P N M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    homEquiv R a d hd M ((tilde.functor (CommRingCat.of N)).map (ModuleCat.ofHom f))=
      (AffineTildePushforward318.iso (CommRingCat.ofHom (algebraMap P N)) M).inv ≫
        (tilde.functor (CommRingCat.of P)).map
          (ModuleCat.ofHom (moduleCounit R a d hd M f)) := by
  letI : Module P M := Module.compHom M (algebraMap P N)
  letI : IsScalarTower P N M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  change AffineFiniteDualSheafAdjunction318.homEquiv P N M
    ((tilde.functor (CommRingCat.of N)).map (ModuleCat.ofHom f) ≫
      (traceSheafIso R a d hd).hom)=_
  rw [AffineFiniteDualSheafAdjunction318.homEquiv_formula,traceSheaf_coordinate]
  rfl
end IntegralNormalTraceSheafDuality318
