module
public import RelativeRefinedCechEffectivity318
public section
noncomputable section
namespace OriginalTestRefinement318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RelativeLineClassBaseChange318
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T T' : Scheme.{u}} (q : C ⟶ B) (b : T ⟶ B) (b' : T' ⟶ B)
  (g : T' ⟶ T) (hg : g ≫ b = b') (r : ActualAffineBaseRefinement318.Refinement g)

include hg in
lemma refined_test : r.lift ≫ b' = r.map ≫ b := by
  rw [← hg,← Category.assoc,r.factor]

/-- Base change the supplied genuine refinement using the original totalMap.
Its factorization is the original totalMap composition identity. -/
@[expose] def refinement : ActualAffineBaseRefinement318.Refinement (totalMap q b b' g hg) where
  source := pullback q (r.map ≫ b)
  map := totalMap q b (r.map ≫ b) r.map rfl
  lift := totalMap q b' (r.map ≫ b) r.lift (refined_test b b' g hg r)
  affine := inferInstance
  flat := inferInstance
  surjective := inferInstance
  factor := by
    have h := totalMap_composition q b b' (r.map ≫ b) g r.lift hg
      (refined_test b b' g hg r) (by rw [r.factor])
    simpa only [r.factor] using h.symm
end OriginalTestRefinement318
