module
public import ContactCartierUniversalAbel318
public section
noncomputable section
namespace ContactCartierFamilyYoneda318
open AlgebraicGeometry CategoryTheory Opposite
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ)) (D : ContactBoundedCartierEquiv318.Data c N b)
/-- The whole actual Cartier family, pulled to every coefficient test. -/
@[expose] def family : yoneda.obj (Over.mk b) ⟶ ContactCartierDataPresheaf318.presheaf c N where
  app T a := ContactBoundedCartierBaseChange318.map c N b T.unop.hom a.left a.w D
  naturality T U f := by
    funext a
    exact (ContactBoundedCartierFunctorial318.map_comp c N b T.unop.hom U.unop.hom D
      a.left a.w f.unop.left f.unop.w).symm
/-- Pulling the universal moduli Abel map along the actual family recovers
the original whole-line Abel transformation, on every test. -/
lemma abel : family c N b D ≫ ContactCartierUniversalAbel318.transformation c N=
    ContactBoundedCartierAbel318.transformation c N b D := by
  ext T a
  exact ContactBoundedCartierAbelNaturality318.test_value c N b T.unop.hom a.left a.w D
/-- Its underlying parameter morphism is the actual classifying map,
not a pointwise replacement with the same geometric fibers. -/
lemma parameter (T : Over (Spec (CommRingCat.of ℚ))) (a : T ⟶ Over.mk b) :
    ((ContactCartierPointPresheaf318.inclusion c N).app (op T)
      ((ContactCartierPresheafEquiv318.equivalence c N).hom.app (op T)
        ((family c N b D).app (op T) a))).left=
      a.left ≫ (ContactBoundedCartierEquiv318.equivalence c N b D).val.val := by
  change (ContactBoundedCartierEquiv318.equivalence c N T.hom
    (ContactBoundedCartierBaseChange318.map c N b T.hom a.left a.w D)).val.val=_
  rw [ContactBoundedCartierNaturality318.natural]
  exact ContactBoundedCartierPointChange318.morphism c N b T.hom a.left a.w _
end ContactCartierFamilyYoneda318
