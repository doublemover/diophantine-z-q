module
public import PELOriginalTranslationLineStabilizer318
public section
noncomputable section
namespace PELOriginalPolarizationClassFaithful318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalPolarizationTransitions318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalTranslationLineClass318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- A genuine line-class stabilizer yields an actual whole sheaf
isomorphism, and therefore the proved original-period obstruction. -/
theorem stabilizer_zero (q : Base τ)
    (h : action τ hτ q (classOf (line τ hτ))=classOf (line τ hτ)) : q=0 := by
  have he : Nonempty ((line τ hτ).object ≅ (translatedLine τ hτ q).object) :=
    (classOf_eq_iff (line τ hτ) (translatedLine τ hτ q)).mp h.symm
  exact PELOriginalTranslationLineStabilizer318.point_zero τ hτ q he.some

/-- The orbit of the original algebraic line under genuine translations
is faithful. Only the honest pullback action law is used here; the
untwisted theorem of square is neither assumed nor inferred. -/
theorem translation_class_injective :
    Function.Injective (fun q : Base τ => action τ hτ q (classOf (line τ hτ))) := by
  intro q r h
  have he := congrArg (action τ hτ (-r)) h
  rw [←action_add,←action_add,neg_add_cancel,action_zero] at he
  have hz := stabilizer_zero τ hτ (-r+q) he
  apply sub_eq_zero.mp
  simpa only [sub_eq_add_neg,add_comm] using hz

/-- The actual translation-difference class map is injective on ALL
original complex points. This is a concrete principality prerequisite,
not a claim that a dual/Picard scheme has been represented. -/
theorem polarization_class_injective : Function.Injective (polarizationClass τ hτ) := by
  intro q r h
  rw [class_formula,class_formula] at h
  exact translation_class_injective τ hτ (mul_right_cancel h)

theorem polarization_class_eq_one (q : Base τ) : polarizationClass τ hτ q=1 ↔ q=0 := by
  constructor
  · intro h
    apply polarization_class_injective τ hτ
    exact h.trans (zero_class τ hτ).symm
  · rintro rfl
    exact zero_class τ hτ

/-- Even an abstract actual whole-sheaf isomorphism between two
translated original lines determines the SAME original point. -/
theorem translated_iso_points (q r : Base τ)
    (E : (translatedLine τ hτ q).object ≅ (translatedLine τ hτ r).object) : q=r := by
  apply translation_class_injective τ hτ
  exact classOf_eq E
end PELOriginalPolarizationClassFaithful318
