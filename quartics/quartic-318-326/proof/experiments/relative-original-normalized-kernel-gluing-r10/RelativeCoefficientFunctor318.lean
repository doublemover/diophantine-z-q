module
public import RelativeCoefficientChange318
public section
noncomputable section
namespace RelativeCoefficientFunctor318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (k R S T B : CommRingCat.{u}) [Algebra k R] [Algebra k S]
  [Algebra k T] [Algebra k B] (f : R →ₐ[k] S) (g : S →ₐ[k] T)

/-- Coefficient identity fixes the entire original tensor ring. -/
lemma ring_identity : RelativeCoefficientChange318.ringMap k R R B (AlgHom.id k R) = 𝟙 _ := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r b => simp [RelativeCoefficientChange318.ringMap]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Actual coefficient chart maps compose in the original ring category. -/
lemma ring_composition : RelativeCoefficientChange318.ringMap k R S B f ≫
    RelativeCoefficientChange318.ringMap k S T B g =
      RelativeCoefficientChange318.ringMap k R T B (g.comp f) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r b => simp [RelativeCoefficientChange318.ringMap]
  | add x y hx hy => simp only [map_add,hx,hy]

variable {X : Scheme.{u}} (p : X ⟶ Spec k)
lemma family_identity : RelativeCoefficientChange318.familyMap k R R (AlgHom.id k R) p = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [RelativeCoefficientChange318.familyMap_original,Category.id_comp]
  · rw [RelativeCoefficientChange318.familyMap_test]
    change _ ≫ Spec.map (𝟙 R) = _
    simp only [Spec.map_id,Category.comp_id,Category.id_comp]

/-- Contravariant composition on the SAME p-first original curve tests. -/
lemma family_composition : RelativeCoefficientChange318.familyMap k S T g p ≫
    RelativeCoefficientChange318.familyMap k R S f p =
      RelativeCoefficientChange318.familyMap k R T (g.comp f) p := by
  apply pullback.hom_ext
  · rw [Category.assoc,RelativeCoefficientChange318.familyMap_original,
      RelativeCoefficientChange318.familyMap_original,RelativeCoefficientChange318.familyMap_original]
  · rw [Category.assoc,RelativeCoefficientChange318.familyMap_test,
      ← Category.assoc,RelativeCoefficientChange318.familyMap_test,
      RelativeCoefficientChange318.familyMap_test,Category.assoc,← Spec.map_comp]
    rfl
end RelativeCoefficientFunctor318
