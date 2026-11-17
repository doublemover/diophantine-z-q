module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public section
noncomputable section
namespace AffineTildeHomEquivalence318
open AlgebraicGeometry CategoryTheory
universe u
variable {R : CommRingCat.{u}} (M N : ModuleCat.{u} R)

/-- Full morphisms between native affine tilde sheaves correspond to
ALL module maps. This uses native fullness and faithfulness, not global
section rank or a selected frame. -/
@[expose] def equivalence : (tilde M ⟶ tilde N) ≃ (M →ₗ[R] N) where
  toFun f := ((tilde.functor R).preimage f).hom
  invFun f := (tilde.functor R).map (ModuleCat.ofHom f)
  left_inv f := (tilde.functor R).map_preimage f
  right_inv f := by
    change ((tilde.functor R).preimage ((tilde.functor R).map (ModuleCat.ofHom f))).hom=f
    rw [Functor.preimage_map]
    rfl

lemma map_value (f : M →ₗ[R] N) :
    equivalence M N ((tilde.functor R).map (ModuleCat.ofHom f))=f :=
  (equivalence M N).apply_symm_apply f

lemma recover (f : tilde M ⟶ tilde N) :
    (tilde.functor R).map (ModuleCat.ofHom (equivalence M N f))=f :=
  (equivalence M N).symm_apply_apply f

variable {C : Type*} [Category C] {X Y Z : C}
/-- Entire Hom sets transported along the specified domain isomorphism. -/
@[expose] def precomposeIso (e : X ≅ Y) : (X ⟶ Z) ≃ (Y ⟶ Z) where
  toFun f := e.inv ≫ f
  invFun g := e.hom ≫ g
  left_inv f := by simp only [←Category.assoc,Iso.hom_inv_id,Category.id_comp]
  right_inv g := by simp only [←Category.assoc,Iso.inv_hom_id,Category.id_comp]

@[expose] def postcomposeIso (e : Y ≅ Z) : (X ⟶ Y) ≃ (X ⟶ Z) where
  toFun f := f ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv f := by simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  right_inv g := by simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
end AffineTildeHomEquivalence318
