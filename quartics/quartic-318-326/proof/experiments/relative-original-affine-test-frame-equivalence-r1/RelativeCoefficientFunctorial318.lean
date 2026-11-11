module
public import RelativeCoefficientCartesian318
public section
noncomputable section
namespace RelativeCoefficientFunctorial318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (k R S T : CommRingCat.{u}) [Algebra k R] [Algebra k S] [Algebra k T]
  (f : R →ₐ[k] S) (g : S →ₐ[k] T) {X : Scheme.{u}} (p : X ⟶ Spec k)
/-- Actual p-first coefficient changes compose with their original
source projections and coefficient maps unchanged. -/
lemma comp : RelativeCoefficientChange318.familyMap k S T g p ≫
    RelativeCoefficientChange318.familyMap k R S f p=
      RelativeCoefficientChange318.familyMap k R T (g.comp f) p := by
  apply pullback.hom_ext
  · simp only [Category.assoc,RelativeCoefficientChange318.familyMap_original]
  · simp only [Category.assoc,RelativeCoefficientChange318.familyMap_test]
    rw [← Spec.map_comp]
    rfl
end RelativeCoefficientFunctorial318
