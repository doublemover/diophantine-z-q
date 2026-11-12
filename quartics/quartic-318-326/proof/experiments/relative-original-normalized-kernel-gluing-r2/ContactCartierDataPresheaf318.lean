module
public import ContactBoundedCartierNaturality318
public import ContactBoundedCartierAbelNaturality318
public section
noncomputable section
namespace ContactCartierDataPresheaf318
open AlgebraicGeometry CategoryTheory Opposite
variable (c : Fin 4 → ℚˣ) (N : ℕ)
/-- Actual full-ideal bounded Cartier families on all coefficient schemes.
The morphisms are literal ideal comaps with the proved Cartier stability. -/
@[expose] def presheaf : (Over (Spec (CommRingCat.of ℚ)))ᵒᵖ ⥤ Type 1 where
  obj T := ContactBoundedCartierEquiv318.Data c N T.unop.hom
  map f := ContactBoundedCartierBaseChange318.map c N _ _ f.unop.left f.unop.w
  map_id T := by
    funext D
    exact ContactBoundedCartierFunctorial318.map_id c N T.unop.hom D
  map_comp f g := by
    funext D
    exact (ContactBoundedCartierFunctorial318.map_comp c N _ _ _ D
      f.unop.left f.unop.w g.unop.left g.unop.w).symm
end ContactCartierDataPresheaf318
