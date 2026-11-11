module
public import ContactBoundedCartierFunctorial318
public section
noncomputable section
namespace ContactBoundedCartierPointChange318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B T : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ)) (t : T ⟶ Spec (CommRingCat.of ℚ))
  (g : T ⟶ B) (hg : g ≫ b=t)
/-- Restrict the ACTUAL Cartier-fiber subset of bounded parameter points.
The genuine Cartier coefficient theorem supplies closure of this subset. -/
@[expose] def map (x : ContactBoundedCartierEquiv318.Point c N b) :
    ContactBoundedCartierEquiv318.Point c N t :=
  ContactBoundedCartierEquiv318.equivalence c N t
    (ContactBoundedCartierBaseChange318.map c N b t g hg
      ((ContactBoundedCartierEquiv318.equivalence c N b).symm x))
/-- Its underlying actual parameter morphism is precisely ordinary
precomposition, not a newly chosen classifying map with equal field values. -/
lemma underlying (x : ContactBoundedCartierEquiv318.Point c N b) :
    (map c N b t g hg x).val=ContactBoundedHilbertNaturality318.pointMap c N b t g hg x.val := by
  change ContactBoundedHilbertEquiv318.equivalence c N t
    (ContactBoundedHilbertBaseChange318.map c N b t g hg
      (ContactBoundedPointFamily318.extract c N b x.val))=_
  rw [ContactBoundedHilbertNaturality318.natural]
  exact congrArg (ContactBoundedHilbertNaturality318.pointMap c N b t g hg)
    ((ContactBoundedHilbertEquiv318.equivalence c N b).apply_symm_apply x.val)
lemma morphism (x : ContactBoundedCartierEquiv318.Point c N b) :
    (map c N b t g hg x).val.val=g ≫ x.val.val :=
  congrArg Subtype.val (underlying c N b t g hg x)
end ContactBoundedCartierPointChange318
