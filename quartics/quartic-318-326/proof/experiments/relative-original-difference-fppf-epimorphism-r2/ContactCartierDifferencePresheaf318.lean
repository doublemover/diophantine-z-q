module
public import ContactCartierAllBoundsPresheaf318
public section
noncomputable section
namespace ContactCartierDifferencePresheaf318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ)
/-- Ordered pairs of actual bounded effective Cartier families, keeping
both full ideals and their potentially different bounds. -/
@[expose] def presheaf : (Over (Spec (CommRingCat.of ℚ)))ᵒᵖ ⥤ Type 1 where
  obj T := (ContactCartierAllBoundsPresheaf318.presheaf c).obj T ×
    (ContactCartierAllBoundsPresheaf318.presheaf c).obj T
  map f D := ((ContactCartierAllBoundsPresheaf318.presheaf c).map f D.1,
    (ContactCartierAllBoundsPresheaf318.presheaf c).map f D.2)
  map_id T := by
    funext D
    simp only [Functor.map_id,types_id_apply]
  map_comp f g := by
    funext D
    simp only [Functor.map_comp,types_comp_apply]
@[expose] def swap : presheaf c ⟶ presheaf c where
  app T D := (D.2,D.1)
  naturality _ _ _ := rfl
lemma swap_twice : swap c ≫ swap c=𝟙 (presheaf c) := rfl
end ContactCartierDifferencePresheaf318
