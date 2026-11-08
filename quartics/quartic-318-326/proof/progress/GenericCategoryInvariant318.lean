module
public import Mathlib.CategoryTheory.Category.Basic
public section
namespace GenericCategoryInvariant318
open CategoryTheory
universe u v
variable {C:Type u} [Category.{v} C]
/-- Factorization through a symmetry preserves any morphism invariant under it. -/
theorem comparison {X Y Z:C} {a b:X ⟶ Y} {s:Y ⟶ Y} {m:Y ⟶ Z}
    (h:a=b ≫ s) (hs:s ≫ m=m) : a ≫ m=b ≫ m := by
  rw [h,Category.assoc,hs]
end GenericCategoryInvariant318
