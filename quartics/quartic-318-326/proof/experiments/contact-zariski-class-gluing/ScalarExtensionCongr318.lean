module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public section
noncomputable section
namespace ScalarExtensionCongr318
open CategoryTheory TensorProduct
open scoped ChangeOfRings
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {f g : R →+* S} (h : f = g)

@[expose] def scalarEquiv : (ModuleCat.restrictScalars f).obj (ModuleCat.of S S) ≃ₗ[R]
    (ModuleCat.restrictScalars g).obj (ModuleCat.of S S) where
  toFun s := s
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r s := by cases h; rfl

@[expose] def component (N : ModuleCat.{u} R) :
    (ModuleCat.extendScalars f).obj N ≅ (ModuleCat.extendScalars g).obj N := by
  let e := TensorProduct.congr (scalarEquiv h) (LinearEquiv.refl R N)
  exact LinearEquiv.toModuleIso
    { e.toAddEquiv with
      map_smul' := by
        intro s z
        induction z using TensorProduct.inductionOn with
        | tmul a n => rfl
        | add z w hz hw =>
            change e (s • z) = s • e z at hz
            change e (s • w) = s • e w at hw
            change e (s • (z + w)) = s • e (z + w)
            simp only [smul_add, map_add, hz, hw] }

lemma component_hom_tmul (N : ModuleCat.{u} R) (s : S) (n : N) :
    (component h N).hom (s ⊗ₜ[R, f] n) = s ⊗ₜ[R, g] n := rfl
lemma component_inv_tmul (N : ModuleCat.{u} R) (s : S) (n : N) :
    (component h N).inv (s ⊗ₜ[R, g] n) = s ⊗ₜ[R, f] n := rfl

/-- Actual scalar extension along equal ring maps, with identity formulas
on every pure tensor. This retains rather than hides the equality transport
needed for the vertices of the actual Cech nerve. -/
@[expose] def naturalIso : ModuleCat.extendScalars f ≅ ModuleCat.extendScalars g :=
  NatIso.ofComponents (component h) (by
    intro N M a
    apply ModuleCat.ExtendScalars.hom_ext
    intro n
    rfl)
end ScalarExtensionCongr318
