module
public import IteratedCoefficientFrameNaturality318
public section
noncomputable section
namespace RelativeFrameRuleBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open IteratedCoefficientFrameModel318 IteratedCoefficientFrameEquivalence318
universe u
variable {X B S : Scheme.{u}} (p : X ⟶ B) (L : Line X) (b : S ⟶ B)
  (F : RelativeFamilyFrameRule318.Rule p L)
/-- Base change of an actual whole-family affine frame rule to an
ARBITRARY coefficient scheme. The canonical model equivalence supplies
full frames on the actual ITERATED families, not just direct-family labels. -/
@[expose] def rule : RelativeFamilyFrameRule318.Rule (projection p b) (originalLine p L b) where
  app R a := (equivalence p L b a).symm (F.app R (a ≫ b))
  natural R T h a a' hh := by
    apply (equivalence p L b a').injective
    rw [IteratedCoefficientFrameNaturality318.natural,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
    exact F.natural R T h (a ≫ b) (a' ≫ b) (by rw [←Category.assoc,hh])
lemma actual_test (R : CommRingCat.{u}) (a : Spec R ⟶ S) :
    equivalence p L b a ((rule p L b F).app R a)=F.app R (a ≫ b) :=
  (equivalence p L b a).apply_symm_apply _
/-- For an original global frame, coefficient change of its complete
rule is EXACTLY the rule of its native geometric pullback. -/
lemma ofFrame (e : Frames L) :
    rule p L b (RelativeFamilyFrameRule318.ofFrame p L e)=
      RelativeFamilyFrameRule318.ofFrame (projection p b) (originalLine p L b)
        (OriginalFramePullback318.frame (original p b) L e) := by
  apply RelativeFamilyFrameEquivalence318.rule_ext
  intro R a
  apply (equivalence p L b a).injective
  rw [actual_test]
  change OriginalFramePullback318.frame (pullback.fst p (a ≫ b)) L e =
    equivalence p L b a (OriginalFramePullback318.frame (inner p b a) (originalLine p L b)
      (OriginalFramePullback318.frame (original p b) L e))
  rw [pullback_frame]
  exact (OriginalFramePullbackCoherence318.path (coefficient p b a) (original p b) L
    (pullback.fst p (a ≫ b)) (RelativeSchemeCoefficient318.map_fst _ _ _ _ _) e).symm
end RelativeFrameRuleBaseChange318
