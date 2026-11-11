module
public import ContactCartierDataPresheaf318
public section
noncomputable section
namespace ContactCartierPointPresheaf318
open AlgebraicGeometry CategoryTheory Opposite
variable (c : Fin 4 → ℚˣ) (N : ℕ)
/-- The genuine Cartier-fiber subfunctor of the ACTUAL represented
bounded quotient parameter. Representability of this subfunctor is not assumed. -/
@[expose] def presheaf : (Over (Spec (CommRingCat.of ℚ)))ᵒᵖ ⥤ Type 1 where
  obj T := ContactBoundedCartierEquiv318.Point c N T.unop.hom
  map f := ContactBoundedCartierPointChange318.map c N _ _ f.unop.left f.unop.w
  map_id T := by
    funext x
    exact ContactBoundedCartierNaturality318.point_id c N T.unop.hom x
  map_comp f g := by
    funext x
    exact (ContactBoundedCartierNaturality318.point_comp c N _ _ _
      f.unop.left f.unop.w g.unop.left g.unop.w x).symm
/-- Forget only the genuine Cartier condition; retain the exact
original parameter morphism on every test, including nonreduced tests. -/
@[expose] def inclusion : presheaf c N ⟶
    yoneda.obj (Over.mk (ContactBoundedHilbertParameter318.structureMap c N)) where
  app T x := Over.homMk x.val.val x.val.property
  naturality T U f := by
    funext x
    apply Over.OverMorphism.ext
    exact ContactBoundedCartierPointChange318.morphism c N _ _ f.unop.left f.unop.w x
lemma inclusion_injective (T : Over (Spec (CommRingCat.of ℚ))) :
    Function.Injective ((inclusion c N).app (op T)) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun f => f.left) h
end ContactCartierPointPresheaf318
