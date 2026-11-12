module
public import ContactNormalizedModuliAbel318
public section
noncomputable section
namespace ContactCartierAllBoundsPresheaf318
open AlgebraicGeometry CategoryTheory Opposite
variable (c : Fin 4 → ℚˣ)
/-- All finite numerical bounds together, with the actual bound retained.
This is not a represented infinite union or an identification of duplicate
families occurring at two bounds. -/
@[expose] def presheaf : (Over (Spec (CommRingCat.of ℚ)))ᵒᵖ ⥤ Type 1 where
  obj T := Σ N : ℕ, ContactBoundedCartierEquiv318.Data c N T.unop.hom
  map f D := ⟨D.1,ContactBoundedCartierBaseChange318.map c D.1 _ _ f.unop.left f.unop.w D.2⟩
  map_id T := by
    funext D
    obtain ⟨N,D⟩ := D
    exact congrArg (Sigma.mk N) (ContactBoundedCartierFunctorial318.map_id c N T.unop.hom D)
  map_comp f g := by
    funext D
    obtain ⟨N,D⟩ := D
    exact congrArg (Sigma.mk N) (ContactBoundedCartierFunctorial318.map_comp c N _ _ _ D
      f.unop.left f.unop.w g.unop.left g.unop.w).symm
@[expose] def inclusion (N : ℕ) : ContactCartierDataPresheaf318.presheaf c N ⟶ presheaf c where
  app T D := ⟨N,D⟩
  naturality _ _ _ := rfl
@[expose] def abel : presheaf c ⟶
    (RelativeFppfLineSheaf318.sheaf (ContactIntrinsicDifferentials318.structureMap c)).obj ⋙
      forget CommGrpCat.{1} where
  app T D := ContactBoundedCartierAbelNaturality318.value c D.1 T.unop.hom D.2
  naturality T U f := by
    funext D
    exact (ContactBoundedCartierAbelNaturality318.natural c D.1 _ _ f.unop.left f.unop.w D.2).symm
lemma bounded (N : ℕ) : inclusion c N ≫ abel c=ContactCartierUniversalAbel318.transformation c N := rfl
end ContactCartierAllBoundsPresheaf318
