module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public section
noncomputable section
namespace AffineTildePushforward318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat.{u} S)

/-- The native pushforward's actual global sections are the original
module with scalars restricted along the SAME ring map. Both directions
come from native top-section and pushforward comparison isomorphisms. -/
@[expose] def globalIso :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)) ≅
      (ModuleCat.restrictScalars φ.hom).obj M := by
  let T := TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
    (evaluation _ _).obj (op (⊤ : (Spec R).Opens))
  exact T.mapIso ((pushforwardCompModulesSpecToSheafIso φ).app (tilde M)) ≪≫
    (ModuleCat.restrictScalars φ.hom).mapIso (tilde.isoTop M).symm

/-- Canonical actual affine pushforward/tilde comparison for ANY
module. No finite-free, projective, or locally free premise is used. -/
@[expose] def iso :
    tilde ((ModuleCat.restrictScalars φ.hom).obj M) ≅
      (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M) := by
  letI : IsIso (tilde M).fromTildeΓ :=
    isIso_fromTildeΓ_iff.mpr ⟨M,⟨Iso.refl _⟩⟩
  letI : IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)).fromTildeΓ :=
    isIso_fromTildeΓ_pushforward φ (tilde M)
  exact (tilde.functor R).mapIso (globalIso φ M).symm ≪≫
    asIso ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)).fromTildeΓ
end AffineTildePushforward318
