module
public import TensorPushoutModule318
public import ScalarExtensionTensor318
public import Mathlib.Algebra.Category.Ring.Basic
public section
noncomputable section
namespace AffineModuleBaseChange318
open CategoryTheory TensorProduct
open scoped ChangeOfRings
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
abbrev ring : CommRingCat.{u} := CommRingCat.of (A ⊗[R] B)
abbrev leftMap : A ⟶ ring R A B := CommRingCat.ofHom (algebraMap A (A ⊗[R] B))
abbrev rightMap : B ⟶ ring R A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
abbrev pushPull : ModuleCat.{u} B ⥤ ModuleCat.{u} A :=
  ModuleCat.extendScalars (rightMap R A B).hom ⋙ ModuleCat.restrictScalars (leftMap R A B).hom
abbrev pullPush : ModuleCat.{u} B ⥤ ModuleCat.{u} A :=
  ModuleCat.restrictScalars (algebraMap R B) ⋙ ModuleCat.extendScalars (algebraMap R A)

local instance moduleR (N : ModuleCat.{u} B) : Module R N :=
  Module.compHom N (algebraMap R B)
local instance towerR (N : ModuleCat.{u} B) : IsScalarTower R B N :=
  IsScalarTower.of_compHom ..

@[expose] def categoricalTensor (N : ModuleCat.{u} B) :
    (pushPull R A B).obj N ≃ₗ[A] (A ⊗[R] B) ⊗[B] N := by
  let e := ScalarExtensionTensor318.tensorEquiv (S := B) (T := A ⊗[R] B) N
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a n
  change ((ModuleCat.extendScalars (rightMap R A B).hom).obj N) at n
  change e (algebraMap A (A ⊗[R] B) a • n) = a • e n
  simp only [e.map_smul, IsScalarTower.algebraMap_smul]

/-- Exact original categorical affine push-pull comparison over the literal
algebra tensor pushout, with all scalar actions explicitly reconciled. -/
@[expose] def component (N : ModuleCat.{u} B) :
    (pushPull R A B).obj N ≅ (pullPush R A B).obj N :=
  LinearEquiv.toModuleIso <|
    (categoricalTensor R A B N).trans <|
      (TensorPushoutModule318.equivalence R A B N).trans
        (ScalarExtensionTensor318.tensorEquiv (S := R) (T := A)
          ((ModuleCat.restrictScalars (algebraMap R B)).obj N)).symm

lemma component_tmul (N : ModuleCat.{u} B) (a : A) (b : B) (n : N) :
    (component R A B N).hom ((a ⊗ₜ[R] b) ⊗ₜ[B, (rightMap R A B).hom] n) =
      a ⊗ₜ[R, algebraMap R A] (b • n) := rfl

lemma component_inv_tmul (N : ModuleCat.{u} B) (a : A) (n : N) :
    (component R A B N).inv (a ⊗ₜ[R, algebraMap R A] n) =
      (a ⊗ₜ[R] (1 : B)) ⊗ₜ[B, (rightMap R A B).hom] n := rfl

@[expose] def naturalIso : pushPull R A B ≅ pullPush R A B :=
  NatIso.ofComponents (component R A B) (by
    intro N M h
    ext z
    change (component R A B M).hom.hom (((pushPull R A B).map h).hom z) =
      ((pullPush R A B).map h).hom ((component R A B N).hom.hom z)
    induction z using TensorProduct.inductionOn with
    | tmul t n =>
        induction t using TensorProduct.inductionOn with
        | tmul a b =>
            change a ⊗ₜ[R, algebraMap R A] (b • h n) =
              a ⊗ₜ[R, algebraMap R A] h (b • n)
            rw [h.hom.map_smul]
        | add t s ht hs => simp only [add_tmul, map_add, ht, hs]
    | add z w hz hw => simp only [map_add, hz, hw])
end AffineModuleBaseChange318
