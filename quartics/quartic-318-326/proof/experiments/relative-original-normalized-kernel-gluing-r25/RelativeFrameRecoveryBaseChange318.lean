module
public import RelativeFrameRuleBaseChange318
public section
noncomputable section
namespace RelativeFrameRecoveryBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open IteratedCoefficientFrameModel318 IteratedCoefficientFrameEquivalence318
universe u
variable {X B S : Scheme.{u}} (p : X ⟶ B) (L : Line X) (b : S ⟶ B)
  (F : RelativeFamilyFrameRule318.Rule p L)
/-- Effective whole-family frame descent commutes with ANY actual scheme
base change. The recovered frame is the native pullback on the SAME whole
original family, not a newly chosen representative of its line class. -/
lemma recovery :
    RelativeFamilyFrameRecovery318.frame (projection p b) (originalLine p L b)
      (RelativeFrameRuleBaseChange318.rule p L b F)=
    OriginalFramePullback318.frame (original p b) L (RelativeFamilyFrameRecovery318.frame p L F) := by
  have h : RelativeFamilyFrameRule318.ofFrame p L
      (RelativeFamilyFrameRecovery318.frame p L F)=F :=
    (RelativeFamilyFrameEquivalence318.equivalence p L).apply_symm_apply F
  have hr := congrArg
    (RelativeFamilyFrameRecovery318.frame (projection p b) (originalLine p L b))
    (RelativeFrameRuleBaseChange318.ofFrame p L b (RelativeFamilyFrameRecovery318.frame p L F))
  rw [h] at hr
  exact hr.trans (RelativeFamilyFrameRecovery318.ofFrame (projection p b) (originalLine p L b)
    (OriginalFramePullback318.frame (original p b) L (RelativeFamilyFrameRecovery318.frame p L F)))
/-- All affine tests of a possibly nonaffine new base recover the exact
original rule after the actual direct/iterated-model comparison. -/
lemma every_test (R : CommRingCat.{u}) (a : Spec R ⟶ S) :
    equivalence p L b a
      (OriginalFramePullback318.frame (inner p b a) (originalLine p L b)
        (OriginalFramePullback318.frame (original p b) L
          (RelativeFamilyFrameRecovery318.frame p L F)))=F.app R (a ≫ b) := by
  rw [←recovery]
  rw [RelativeFamilyFrameRecovery318.family_test]
  exact RelativeFrameRuleBaseChange318.actual_test p L b F R a
end RelativeFrameRecoveryBaseChange318
