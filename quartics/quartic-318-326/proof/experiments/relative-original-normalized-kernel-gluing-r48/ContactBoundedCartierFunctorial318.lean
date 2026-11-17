module
public import ContactBoundedCartierBaseChange318
public section
noncomputable section
namespace ContactBoundedCartierFunctorial318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B T U : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ)) (t : T ⟶ Spec (CommRingCat.of ℚ))
  (u : U ⟶ Spec (CommRingCat.of ℚ)) (D : ContactBoundedCartierEquiv318.Data c N b)
/-- The retained whole ideal, not just its support or line class, obeys
the identity law on the genuine all-scheme Cartier domain. -/
lemma map_id : ContactBoundedCartierBaseChange318.map c N b b (𝟙 B) (Category.id_comp b) D=D := by
  apply Subtype.ext
  exact ContactBoundedHilbertFunctorial318.map_id c N b D.val
lemma map_comp (g : T ⟶ B) (hg : g ≫ b=t) (h : U ⟶ T) (hh : h ≫ t=u) :
    ContactBoundedCartierBaseChange318.map c N t u h hh
      (ContactBoundedCartierBaseChange318.map c N b t g hg D)=
      ContactBoundedCartierBaseChange318.map c N b u (h ≫ g)
        (by rw [Category.assoc,hg]; exact hh) D := by
  apply Subtype.ext
  exact ContactBoundedHilbertFunctorial318.map_comp c N b t u D.val g hg h hh
end ContactBoundedCartierFunctorial318
