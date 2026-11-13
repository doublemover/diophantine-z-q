module
public import ScalarExtensionCongr318
public section
noncomputable section
namespace ScalarExtensionComposition318
open CategoryTheory TensorProduct
open scoped ChangeOfRings
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* S) (g : S →+* T) (N : ModuleCat.{u} R)

/-- The original composition comparison retains the entire pure tensor,
not just the image of unit tensors. -/
lemma hom_tmul (t : T) (n : N) :
    (ModuleCat.extendScalarsComp f g).hom.app N (t ⊗ₜ[R, g.comp f] n) =
      t ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n) := by
  have h : t ⊗ₜ[R, g.comp f] n =
      t • ((1 : T) ⊗ₜ[R, g.comp f] n) := by
    simp only [smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, ModuleCat.extendScalarsComp_hom_app_one_tmul]
  change t • ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n)) =
    t ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n)
  simp only [smul_tmul', smul_eq_mul, mul_one]

lemma inv_tmul (t : T) (s : S) (n : N) :
    (ModuleCat.extendScalarsComp f g).inv.app N
        (t ⊗ₜ[S, g] (s ⊗ₜ[R, f] n)) =
      (t * g s) ⊗ₜ[R, g.comp f] n := by
  apply ((ModuleCat.extendScalarsComp f g).app N).toLinearEquiv.injective
  change (ModuleCat.extendScalarsComp f g).hom.app N
    ((ModuleCat.extendScalarsComp f g).inv.app N (t ⊗ₜ[S, g] (s ⊗ₜ[R, f] n))) =
      (ModuleCat.extendScalarsComp f g).hom.app N ((t * g s) ⊗ₜ[R, g.comp f] n)
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id_app, ModuleCat.id_apply, hom_tmul]
  have h : s ⊗ₜ[R, f] n = s • ((1 : S) ⊗ₜ[R, f] n) := by
    simp only [smul_tmul', smul_eq_mul, mul_one]
  rw [h, ← TensorProduct.smul_tmul]
  congr 1
  change g s * t = t * g s
  exact mul_comm _ _

/-- Canonical iterated scalar extension across an actual commuting pair
of maps, with the original ring-map equality explicitly retained. -/
@[expose] def comparison (h : R →+* T) (hh : g.comp f = h) :
    (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g).obj N ≅
      (ModuleCat.extendScalars h).obj N :=
  ((ModuleCat.extendScalarsComp f g).app N).symm ≪≫
    ScalarExtensionCongr318.component hh N

lemma comparison_tmul (h : R →+* T) (hh : g.comp f = h)
    (t : T) (s : S) (n : N) :
    (comparison f g N h hh).hom (t ⊗ₜ[S, g] (s ⊗ₜ[R, f] n)) =
      (t * g s) ⊗ₜ[R, h] n := by
  change (ScalarExtensionCongr318.component hh N).hom
    ((ModuleCat.extendScalarsComp f g).inv.app N _) = _
  rw [inv_tmul, ScalarExtensionCongr318.component_hom_tmul]

lemma comparison_inv_tmul (h : R →+* T) (hh : g.comp f = h)
    (t : T) (n : N) :
    (comparison f g N h hh).inv (t ⊗ₜ[R, h] n) =
      t ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n) := by
  change (ModuleCat.extendScalarsComp f g).hom.app N
    ((ScalarExtensionCongr318.component hh N).inv _) = _
  rw [ScalarExtensionCongr318.component_inv_tmul, hom_tmul]
/-- Canonical scalar extension across a split composite is the original
module, through the actual composition and identity comparisons. -/
@[expose] def splitIso (f : R →+* S) (g : S →+* R) (h : g.comp f = RingHom.id R)
    (N : ModuleCat.{u} R) :
    (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj N) ≅ N :=
  comparison f g N (RingHom.id R) h ≪≫ (ModuleCat.extendScalarsId R).app N

lemma identity_tmul (N : ModuleCat.{u} R) (r : R) (n : N) :
    (ModuleCat.extendScalarsId R).hom.app N (r ⊗ₜ[R, RingHom.id R] n) = r • n := by
  have hr : r ⊗ₜ[R, RingHom.id R] n =
      r • ((1 : R) ⊗ₜ[R, RingHom.id R] n) := by
    simp only [smul_tmul', smul_eq_mul, mul_one]
  rw [hr, map_smul, ModuleCat.extendScalarsId_hom_app_one_tmul]

lemma splitIso_hom_tmul (f : R →+* S) (g : S →+* R) (h : g.comp f = RingHom.id R)
    (N : ModuleCat.{u} R) (r : R) (s : S) (n : N) :
    (splitIso f g h N).hom (r ⊗ₜ[S, g] (s ⊗ₜ[R, f] n)) = (r * g s) • n := by
  change (ModuleCat.extendScalarsId R).hom.app N ((comparison f g N _ h).hom _) = _
  rw [comparison_tmul, identity_tmul]

lemma splitIso_inv_apply (f : R →+* S) (g : S →+* R) (h : g.comp f = RingHom.id R)
    (N : ModuleCat.{u} R) (n : N) :
    (splitIso f g h N).inv n = (1 : R) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n) := by
  change (comparison f g N _ h).inv ((ModuleCat.extendScalarsId R).inv.app N n) = _
  rw [ModuleCat.extendScalarsId_inv_app_apply, comparison_inv_tmul]

end ScalarExtensionComposition318
