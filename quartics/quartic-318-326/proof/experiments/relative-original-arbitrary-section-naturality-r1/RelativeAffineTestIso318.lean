module
public import RelativeAffineTestExt318
public section
noncomputable section
namespace RelativeAffineTestIso318
open AlgebraicGeometry CategoryTheory
open RelativeAffineTestRule318 RelativeAffineTestGluing318 RelativeAffineTestEvaluation318
universe u
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ Spec (CommRingCat.of R))
  (F : Rule R p q) (G : Rule R q p)
  (hF : ∀ (S : CommRingCat.{u}) [Algebra R S] (x : Test R p S),G.app S (F.app S x)=x)
  (hG : ∀ (S : CommRingCat.{u}) [Algebra R S] (y : Test R q S),F.app S (G.app S y)=y)
lemma forward_inverse : realize R p q F ≫ realize R q p G=𝟙 X := by
  apply RelativeAffineTestExt318.hom_ext R p
  intro S _ x
  rw [← Category.assoc,evaluate,evaluate,Category.comp_id]
  exact congrArg Subtype.val (hF S x)
lemma inverse_forward : realize R q p G ≫ realize R p q F=𝟙 Y := by
  apply RelativeAffineTestExt318.hom_ext R q
  intro S _ y
  rw [← Category.assoc,evaluate,evaluate,Category.comp_id]
  exact congrArg Subtype.val (hG S y)
/-- Two inverse natural affine-test operations yield actual scheme
isomorphisms by explicit whole-cover realization and equality detection. -/
@[expose] def iso : X ≅ Y where
  hom := realize R p q F
  inv := realize R q p G
  hom_inv_id := forward_inverse R p q F G hF
  inv_hom_id := inverse_forward R p q F G hG
end RelativeAffineTestIso318
