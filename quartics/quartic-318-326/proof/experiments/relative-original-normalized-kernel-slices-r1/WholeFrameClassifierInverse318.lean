module
public import WholeParameterFrameRecovery318
public section
noncomputable section
namespace WholeFrameClassifierInverse318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open IteratedCoefficientFrameModel318 IteratedCoefficientFrameEquivalence318
universe u
variable {X B Y T : Scheme.{u}} (p : X ⟶ B) (L : Line X) (q : Y ⟶ B)
  (E : AffineRelativeFrameClassifier318.Data p L q) (b : T ⟶ B)
lemma classify_recover (z : T ⟶ Y) (hz : z ≫ q=b) :
    WholeFrameClassifyingRule318.classify p L q E b
      (WholeParameterFrameRecovery318.recover p L q E b z hz)=z := by
  apply SchemeAffineMorphismEvaluation318.hom_ext
  intro R a
  rw [WholeFrameClassifyingRule318.test]
  change ((E.equivalence R (a ≫ b)).symm
    (equivalence p L b a (OriginalFramePullback318.frame (inner p b a) (originalLine p L b)
      (WholeParameterFrameRecovery318.recover p L q E b z hz)))).val=a ≫ z
  rw [WholeParameterFrameRecovery318.test,Equiv.symm_apply_apply]
  rfl
lemma recover_classify (e : Frames (originalLine p L b)) :
    WholeParameterFrameRecovery318.recover p L q E b
      (WholeFrameClassifyingRule318.classify p L q E b e)
      (WholeFrameClassifyingRule318.over p L q E b e)=e := by
  apply (RelativeFamilyFrameEquivalence318.equivalence (projection p b) (originalLine p L b)).injective
  apply RelativeFamilyFrameEquivalence318.rule_ext
  intro R a
  change OriginalFramePullback318.frame (inner p b a) (originalLine p L b)
    (WholeParameterFrameRecovery318.recover p L q E b
      (WholeFrameClassifyingRule318.classify p L q E b e)
      (WholeFrameClassifyingRule318.over p L q E b e))=
    OriginalFramePullback318.frame (inner p b a) (originalLine p L b) e
  apply (equivalence p L b a).injective
  rw [WholeParameterFrameRecovery318.test]
  have hp : WholeParameterFrameRecovery318.localPoint q b
      (WholeFrameClassifyingRule318.classify p L q E b e)
      (WholeFrameClassifyingRule318.over p L q E b e) R a=
      WholeFrameClassifyingRule318.localPoint p L q E b e R a := by
    apply Subtype.ext
    exact WholeFrameClassifyingRule318.test p L q E b e R a
  rw [hp,WholeFrameClassifyingRule318.localPoint,Equiv.apply_symm_apply]
  rfl
/-- Effective whole-scheme classification. No global representability was
an input: affine classification plus native original frame descent suffice. -/
@[expose] def equivalence : {z : T ⟶ Y // z ≫ q=b} ≃ Frames (originalLine p L b) where
  toFun z := WholeParameterFrameRecovery318.recover p L q E b z.val z.property
  invFun e := ⟨WholeFrameClassifyingRule318.classify p L q E b e,
    WholeFrameClassifyingRule318.over p L q E b e⟩
  left_inv z := Subtype.ext (classify_recover p L q E b z.val z.property)
  right_inv e := recover_classify p L q E b e
end WholeFrameClassifierInverse318
