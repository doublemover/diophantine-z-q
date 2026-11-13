module
public import IntegralNormalTraceSheafDuality318
public import IntegralNormalSourceDifferentialFrame318
public section
noncomputable section
namespace IntegralNormalDifferentialDuality318
open AlgebraicGeometry CategoryTheory Polynomial IntegralDistinctContactOpen318
universe u
variable (R : Type u) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "π" => AffineFiniteDualSheafAdjunction318.projection P N

/-- Actual base differentials, with the literal polynomial dT generator. -/
@[expose] def baseIso :
    tilde (R:=CommRingCat.of P) (ModuleCat.of P P) ≅
      tilde (R:=CommRingCat.of P) (ModuleCat.of P (KaehlerDifferential R P)) :=
  (tilde.functor (CommRingCat.of P)).mapIso
    (KaehlerDifferential.polynomialEquiv R).symm.toModuleIso

/-- Affine finite duality now has the genuine base differential sheaf
as target, rather than a coefficient sheaf with an unspecified frame. -/
@[expose] def homEquiv (M : ModuleCat.{u} N) :
    (tilde M ⟶ IntegralNormalTraceSheafDuality318.traceSheaf R a d) ≃
      ((Scheme.Modules.pushforward π).obj (tilde M) ⟶
        tilde (R:=CommRingCat.of P) (ModuleCat.of P (KaehlerDifferential R P))) :=
  (IntegralNormalTraceSheafDuality318.homEquiv R a d hd M).trans
    (AffineTildeHomEquivalence318.postcomposeIso (baseIso R))

theorem homEquiv_formula (M : ModuleCat.{u} N)
    (f : tilde M ⟶ IntegralNormalTraceSheafDuality318.traceSheaf R a d) :
    homEquiv R a d hd M f =
      IntegralNormalTraceSheafDuality318.homEquiv R a d hd M f ≫ (baseIso R).hom := rfl

/-- The transported trace functional is multiplied by dT, not by an
unrecorded unit. The full module counit was produced in the predecessor. -/
theorem base_coefficient (p : P) :
    (KaehlerDifferential.polynomialEquiv R).symm p =
      p • KaehlerDifferential.D R P X := by
  apply (KaehlerDifferential.polynomialEquiv R).injective
  rw [LinearEquiv.apply_symm_apply,map_smul,
    KaehlerDifferential.polynomialEquiv_D,Polynomial.derivative_X,smul_eq_mul,mul_one]

theorem existsUnique_lift (M : ModuleCat.{u} N)
    (g : (Scheme.Modules.pushforward π).obj (tilde M) ⟶
      tilde (R:=CommRingCat.of P) (ModuleCat.of P (KaehlerDifferential R P))) :
    ∃! f, homEquiv R a d hd M f=g := by
  refine ⟨(homEquiv R a d hd M).symm g,(homEquiv R a d hd M).apply_symm_apply g,?_⟩
  intro f hf
  exact (homEquiv R a d hd M).injective
    (hf.trans ((homEquiv R a d hd M).apply_symm_apply g).symm)
end IntegralNormalDifferentialDuality318
