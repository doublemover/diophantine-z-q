module
public import RelativeAffineTestEvaluation318
public section
noncomputable section
namespace RelativeAffineTestExt318
open AlgebraicGeometry CategoryTheory
open RelativeAffineTestRule318
universe u
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of R)) (f g : X ⟶ Y)
/-- Affine relative test morphisms detect equality on the WHOLE scheme.
This is a cover theorem, not a geometric-point extensionality claim. -/
lemma hom_ext (h : ∀ (S : CommRingCat.{u}) [Algebra R S] (x : Test R p S),x.val ≫ f=x.val ≫ g) : f=g := by
  let U := RelativeAffineTestCover318.cover R p
  letI (i : U.I₀) : Algebra R (U.X i) := RelativeAffineTestCover318.algebra R p i
  apply Scheme.Cover.hom_ext U.openCover _ _
  intro i
  exact h _ (RelativeAffineTestCover318.point R p i)
end RelativeAffineTestExt318
