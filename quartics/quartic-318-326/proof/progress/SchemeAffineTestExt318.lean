module
public import Mathlib.AlgebraicGeometry.Gluing
public section
namespace SchemeAffineTestExt318
open AlgebraicGeometry CategoryTheory
universe u
/-- Equality on all affine test schemes implies literal equality of Scheme
morphisms. Affine tests retain nonreduced directions and are not field points. -/
theorem hom_ext {X Y:Scheme.{u}} (f g:X ⟶ Y)
    (h:∀ (A:CommRingCat.{u}) (a:Spec A ⟶ X), a ≫ f=a ≫ g) : f=g := by
  apply X.affineOpenCover.openCover.hom_ext
  intro i
  exact h (X.affineOpenCover.X i) (X.affineOpenCover.f i)
end SchemeAffineTestExt318
