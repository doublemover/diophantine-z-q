module
public import ContactBoundedCartierPointChange318
public section
noncomputable section
namespace ContactBoundedCartierNaturality318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B T U : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ)) (t : T ⟶ Spec (CommRingCat.of ℚ))
  (u : U ⟶ Spec (CommRingCat.of ℚ))
/-- The genuine Cartier restriction of the original bounded Hilbert
equivalence is now natural on ALL scheme tests, for literal whole ideal
comap and literal parameter precomposition. -/
lemma natural (g : T ⟶ B) (hg : g ≫ b=t) (D : ContactBoundedCartierEquiv318.Data c N b) :
    ContactBoundedCartierEquiv318.equivalence c N t (ContactBoundedCartierBaseChange318.map c N b t g hg D)=
      ContactBoundedCartierPointChange318.map c N b t g hg (ContactBoundedCartierEquiv318.equivalence c N b D) := by
  rw [ContactBoundedCartierPointChange318.map,Equiv.symm_apply_apply]
lemma point_id (x : ContactBoundedCartierEquiv318.Point c N b) :
    ContactBoundedCartierPointChange318.map c N b b (𝟙 B) (Category.id_comp b) x=x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [ContactBoundedCartierPointChange318.morphism,Category.id_comp]
lemma point_comp (g : T ⟶ B) (hg : g ≫ b=t) (h : U ⟶ T) (hh : h ≫ t=u)
    (x : ContactBoundedCartierEquiv318.Point c N b) :
    ContactBoundedCartierPointChange318.map c N t u h hh
      (ContactBoundedCartierPointChange318.map c N b t g hg x)=
      ContactBoundedCartierPointChange318.map c N b u (h ≫ g) (by rw [Category.assoc,hg]; exact hh) x := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [ContactBoundedCartierPointChange318.morphism,Category.assoc]
end ContactBoundedCartierNaturality318
