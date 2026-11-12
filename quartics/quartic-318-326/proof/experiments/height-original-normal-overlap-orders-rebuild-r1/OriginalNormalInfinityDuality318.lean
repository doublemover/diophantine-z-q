module
public import OriginalNormalInfinitySameCenter318
public section
noncomputable section
namespace OriginalNormalInfinityDuality318
open AlgebraicGeometry CategoryTheory NumberField Polynomial
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalInfinityOrder318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "P" => Polynomial R
local notation "C" => Order c t w D

abbrev projection := Spec.map (CommRingCat.ofHom (polynomialScalar c t w D))
lemma finite_projection : IsFinite (projection c t w D) :=
  IsFinite.SpecMap_iff.mpr (finite_polynomial c t w D)

/-- Entire native coinduced dual on the actual reciprocal NORMAL order,
with its explicit reciprocal polynomial scalar and multiplication action.
No trace-lattice identification at infinity is smuggled into this object. -/
@[expose] def dualSheaf : (Spec (CommRingCat.of C)).Modules := by
  letI : Algebra P C := (polynomialScalar c t w D).toAlgebra
  exact AffineFiniteDualSheafAdjunction318.dualSheaf P C

/-- Genuine infinity-chart affine duality for every module and every
native sheaf morphism, targeting actual base dS. -/
@[expose] def homEquiv (Q : ModuleCat C) :
    (tilde Q ⟶ dualSheaf c t w D) ≃
      ((Scheme.Modules.pushforward (projection c t w D)).obj (tilde Q) ⟶
        tilde (R:=CommRingCat.of P) (ModuleCat.of P (KaehlerDifferential R P))) := by
  letI : Algebra P C := (polynomialScalar c t w D).toAlgebra
  exact (AffineFiniteDualSheafAdjunction318.homEquiv P C Q).trans
    (AffineTildeHomEquivalence318.postcomposeIso (IntegralNormalDifferentialDuality318.baseIso R))

/-- The precise original infinity structural square is retained. -/
theorem original_projection : OriginalNormalInfinityChart318.chart c t w D M ≫ M.projection=
    projection c t w D ≫ JLineAtlas318.chart R 0 :=
  OriginalNormalInfinityChart318.base c t w D M

theorem existsUnique_lift (Q : ModuleCat C)
    (g : (Scheme.Modules.pushforward (projection c t w D)).obj (tilde Q) ⟶
      tilde (R:=CommRingCat.of P) (ModuleCat.of P (KaehlerDifferential R P))) :
    ∃! f, homEquiv c t w D Q f=g := by
  refine ⟨(homEquiv c t w D Q).symm g,(homEquiv c t w D Q).apply_symm_apply g,?_⟩
  intro f hf
  exact (homEquiv c t w D Q).injective
    (hf.trans ((homEquiv c t w D Q).apply_symm_apply g).symm)

/-- Its counit is the WHOLE functional evaluated at1, then multiplied
by the literal polynomial dS and sheafified through native pushforward.
There is no premise identifying this with a generic trace coefficient. -/
theorem counit_formula (Q : ModuleCat C) (f : tilde Q ⟶ dualSheaf c t w D) :
    letI : Algebra P C := (polynomialScalar c t w D).toAlgebra
    letI : Module P Q := Module.compHom Q (algebraMap P C)
    letI : IsScalarTower P C Q := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    homEquiv c t w D Q f =
      (AffineTildePushforward318.iso (CommRingCat.ofHom (polynomialScalar c t w D)) Q).inv ≫
        (tilde.functor (CommRingCat.of P)).map (ModuleCat.ofHom
          (FiniteDualAdjunction318.evaluateOne
            (AffineTildeHomEquivalence318.equivalence Q
              (ModuleCat.of C (FiniteDualModuleAction318.Dual P C)) f))) ≫
          (IntegralNormalDifferentialDuality318.baseIso R).hom := by
  letI : Algebra P C := (polynomialScalar c t w D).toAlgebra
  letI : Module P Q := Module.compHom Q (algebraMap P C)
  letI : IsScalarTower P C Q := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  change AffineFiniteDualSheafAdjunction318.homEquiv P C Q f ≫
    (IntegralNormalDifferentialDuality318.baseIso R).hom=_
  rw [AffineFiniteDualSheafAdjunction318.homEquiv_formula,Category.assoc]
end OriginalNormalInfinityDuality318
