module
public import IteratedCoefficientFrameEquivalence318
public section
noncomputable section
namespace IteratedCoefficientFrameNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open IteratedCoefficientFrameModel318 IteratedCoefficientFrameEquivalence318
universe u
variable {X B S T T' : Scheme.{u}} (p : X ⟶ B) (L : Line X)
  (b : S ⟶ B) (a : T ⟶ S) (a' : T' ⟶ S) (h : T' ⟶ T) (hh : h ≫ a=a')
lemma nested_source : nestedChange p b a a' h hh ≫ composite p b a=composite p b a' := by
  rw [composite,←Category.assoc,RelativeSchemeCoefficient318.map_fst]
  rfl
/-- The full original nested-to-direct frame equivalence is natural for
EVERY actual scheme coefficient arrow, including nonflat and nilpotent tests. -/
lemma natural (e : Frames (nestedLine p L b a)) :
    equivalence p L b a' (OriginalFramePathTransport318.transport (originalLine p L b)
      (nestedChange p b a a' h hh) (inner p b a) (inner p b a')
      (RelativeSchemeCoefficient318.map_fst _ _ _ _ _) e)=
    OriginalFramePathTransport318.transport L (directChange p b a a' h hh)
      (pullback.fst p (a ≫ b)) (pullback.fst p (a' ≫ b))
      (RelativeSchemeCoefficient318.map_fst _ _ _ _ _) (equivalence p L b a e) := by
  rw [forward,forward]
  rw [OriginalNestedFrameFlatten318.natural]
  rw [flattened_forward,flattened_forward]
  exact OriginalFrameModelNaturality318.natural L (model p b a).hom (model p b a').hom
    (directChange p b a a' h hh) (nestedChange p b a a' h hh)
    (pullback.fst p (a ≫ b)) (composite p b a)
    (pullback.fst p (a' ≫ b)) (composite p b a')
    (model_source p b a) (model_source p b a')
    (RelativeSchemeCoefficient318.map_fst _ _ _ _ _)
    (nested_source p b a a' h hh) (model_square p b a a' h hh) _
end IteratedCoefficientFrameNaturality318
