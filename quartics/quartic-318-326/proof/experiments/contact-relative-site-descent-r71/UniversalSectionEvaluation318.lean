module
public import UniversalStructurePushforward318
public import RelativeSectionBaseChange318
public section
noncomputable section
namespace UniversalSectionEvaluation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S T : Scheme.{u}} (p : X ⟶ S) (e : S ⟶ X) (hs : e ≫ p = 𝟙 S)

include hs in
lemma section_appTop_isIso [IsIso p.appTop] : IsIso e.appTop := by
  have h : p.appTop ≫ e.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hs]; rfl
  have hi : IsIso (p.appTop ≫ e.appTop) := by rw [h]; infer_instance
  exact (isIso_comp_left_iff _ _).mp hi

include hs in
lemma section_appTop_bijective [IsIso p.appTop] : Function.Bijective e.appTop := by
  let := section_appTop_isIso p e hs
  exact ConcreteCategory.bijective_of_isIso _

include hs in
/-- The actual pulled-back section evaluates global functions bijectively
on every flat scheme test when universal structure pushforward applies. -/
lemma test_evaluation_bijective [IsAffine S] [IsProper p] [IsIso p.appTop]
    (b : T ⟶ S) [Flat b] : Function.Bijective
      (RelativeSectionBaseChange318.sectionOn p e hs b).appTop := by
  let : IsIso (pullback.snd p b).appTop :=
    UniversalStructurePushforward318.baseChange_app_isIso p b ⊤
  exact section_appTop_bijective _ _ (RelativeSectionBaseChange318.sectionOn_snd p e hs b)
end UniversalSectionEvaluation318
