module
public import AffineTildeHomEquivalence318
public import AffineTildePushforward318
public import FiniteDualAdjunction318
public section
noncomputable section
namespace AffineFiniteDualSheafAdjunction318
open AlgebraicGeometry CategoryTheory
universe u
variable (P N : Type u) [CommRing P] [CommRing N] [Algebra P N]
local notation "φ" => CommRingCat.ofHom (algebraMap P N)
local notation "D" => FiniteDualModuleAction318.Dual P N

/-- Actual native affine projection, retaining the exact scalar map. -/
abbrev projection := Spec.map φ
abbrev dualSheaf := tilde (R:=CommRingCat.of N) (ModuleCat.of N D)

/-- Affine sheaf duality for EVERY N-module M: maps to the ENTIRE
finite-dual sheaf correspond to maps from its ACTUAL native pushforward
to the base structure module. No finite-free/projective hypothesis on M
or N is required for this Hom-set formula. -/
@[expose] def homEquiv (M : ModuleCat.{u} N) :
    (tilde M ⟶ dualSheaf P N) ≃
      ((Scheme.Modules.pushforward (projection P N)).obj (tilde M) ⟶
        tilde (R:=CommRingCat.of P) (ModuleCat.of P P)) := by
  letI : Module P M := Module.compHom M (algebraMap P N)
  letI : IsScalarTower P N M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let MP := (ModuleCat.restrictScalars (algebraMap P N)).obj M
  exact (AffineTildeHomEquivalence318.equivalence M (ModuleCat.of N D)).trans
    (FiniteDualAdjunction318.homEquiv.trans
      ((AffineTildeHomEquivalence318.equivalence MP (ModuleCat.of P P)).symm.trans
        (AffineTildeHomEquivalence318.precomposeIso (AffineTildePushforward318.iso φ M))))

/-- The displayed correspondence is literal coinduction evaluation at
one, then native sheafification and the specified pushforward comparison. -/
theorem homEquiv_formula (M : ModuleCat.{u} N) (f : tilde M ⟶ dualSheaf P N) :
    letI : Module P M := Module.compHom M (algebraMap P N)
    letI : IsScalarTower P N M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    homEquiv P N M f=(AffineTildePushforward318.iso φ M).inv ≫
      (tilde.functor (CommRingCat.of P)).map (ModuleCat.ofHom
        (FiniteDualAdjunction318.evaluateOne
          (AffineTildeHomEquivalence318.equivalence M (ModuleCat.of N D) f))) := rfl

/-- Every actual base-sheaf map has a unique full dual-valued lift.
This quantifies all module inputs and all sheaf morphisms, not a frame. -/
theorem existsUnique_lift (M : ModuleCat.{u} N)
    (g : (Scheme.Modules.pushforward (projection P N)).obj (tilde M) ⟶
      tilde (R:=CommRingCat.of P) (ModuleCat.of P P)) :
    ∃! f : tilde M ⟶ dualSheaf P N,homEquiv P N M f=g := by
  refine ⟨(homEquiv P N M).symm g,(homEquiv P N M).apply_symm_apply g,?_⟩
  intro f hf
  apply (homEquiv P N M).injective
  exact hf.trans ((homEquiv P N M).apply_symm_apply g).symm
end AffineFiniteDualSheafAdjunction318
