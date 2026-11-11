module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public section
noncomputable section
namespace TildeFramedTop318
open AlgebraicGeometry CategoryTheory
universe u
variable (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]

/-- The tilde unit's top-section map is the actual affine scalar map. -/
lemma unit_top (r : A) :
    (tilde.isoTop (R:=CommRingCat.of A) (ModuleCat.of A A)).hom r =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv r := rfl

/-- Naturality identifies the actual sheafified frame with the original
whole-module frame at top sections, retaining the exact ΓSpec scalar map. -/
lemma frame_top (e : A ≃ₗ[A] M) (r : A) :
    (tilde.isoTop (R:=CommRingCat.of A) (ModuleCat.of A M)).inv
      (((tilde.functor (CommRingCat.of A)).map e.toModuleIso.hom).app ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv r)) = e r := by
  have h := congrArg (fun f => f r)
    ((tilde.toTildeΓNatIso (R:=CommRingCat.of A)).hom.naturality e.toModuleIso.hom)
  change (tilde.isoTop (R:=CommRingCat.of A) (ModuleCat.of A M)).hom (e r) =
    ((tilde.functor (CommRingCat.of A)).map e.toModuleIso.hom).app ⊤
      ((tilde.isoTop (R:=CommRingCat.of A) (ModuleCat.of A A)).hom r) at h
  rw [unit_top] at h
  rw [←h]
  exact Iso.hom_inv_id_apply _ _

lemma frame_section (e : A ≃ₗ[A] M) (s : Γ(Spec (CommRingCat.of A),⊤)) :
    (tilde.isoTop (R:=CommRingCat.of A) (ModuleCat.of A M)).inv
      (((tilde.functor (CommRingCat.of A)).map e.toModuleIso.hom).app ⊤ s) =
      e ((Scheme.ΓSpecIso (CommRingCat.of A)).hom s) := by
  have h := frame_top A M e ((Scheme.ΓSpecIso (CommRingCat.of A)).hom s)
  rw [Iso.hom_inv_id_apply] at h
  exact h
end TildeFramedTop318
