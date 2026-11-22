module

public import SelectedSameAActualPushforwardRestriction318
public import AffineSpecFreePushforward318
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
The actual middle module, in one actual affine dual-number chart.
The standard trivial frame is transported from the real normalized
line. The affine middle is recovered by its genuine global sections,
not an arbitrary replacement by a free module.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace SelectedSameAPrincipalUnitMiddleChart318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A X : Scheme.{u}} (p : X ⟶ A) (B : Type u) [CommRing B]
abbrev S (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
abbrev D := TrivSqZeroExt B B
abbrev q : S (D B) ⟶ S B :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom B B))

variable (j : S B ⟶ A) (jD : S (D B) ⟶ X)
variable [IsOpenImmersion j] [IsOpenImmersion jD]
variable (H : IsPullback (q B) jD j p) (M : X.Modules)
variable (F : SheafOfModules.unit (S (D B)).ringCatSheaf ≅ M.restrict jD)

abbrev actualObject := ((Scheme.Modules.pushforward p).obj M).restrict j

/-- Genuine open restriction comparison followed by pushforward of
the one actual line frame. The two sheaf factors have the same point
and frame; no new affine model or arbitrary basis is picked. -/
@[expose] def chartMiddle :
    actualObject p B j M ≅ AffineSpecFreePushforward318.object (CommRingCat.of B) (CommRingCat.of (D B)) :=
  SelectedSameAActualPushforwardRestriction318.iso (q B) jD j p H M ≪≫
    (Scheme.Modules.pushforward (q B)).mapIso F.symm

include H F in
theorem actual_fromTilde_isIso : IsIso (actualObject p B j M).fromTildeΓ := by
  let N := AffineSpecFreePushforward318.object (CommRingCat.of B) (CommRingCat.of (D B))
  letI : IsIso N.fromTildeΓ :=
    AffineSpecFreePushforward318.fromTilde_isIso
      (CommRingCat.of B) (CommRingCat.of (D B))
  exact isIso_fromTildeΓ_iff.mpr
    ⟨_, ⟨asIso N.fromTildeΓ ≪≫ (chartMiddle p B j jD H M F).symm⟩⟩

/-- Exact B-linear top coordinate of the original middle module:
the given open comparison, the given frame, and the literal Spec
affine coefficient, with no chosen inverse to an unknown comparison. -/
@[expose] def topCoordinates :
    (moduleSpecΓFunctor (R := CommRingCat.of B)).obj
        (actualObject p B j M) ≅ ModuleCat.of B (D B) :=
  (moduleSpecΓFunctor (R := CommRingCat.of B)).mapIso
      (chartMiddle p B j jD H M F) ≪≫
    (AffineSpecFreePushforward318.globalsEquiv
      (CommRingCat.of B) (CommRingCat.of (D B))).toModuleIso

end SelectedSameAPrincipalUnitMiddleChart318
