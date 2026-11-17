module
public import ContactWholeSchemeFrameParameter318
public section
noncomputable section
namespace WholeFrameCoefficientNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open IteratedCoefficientFrameModel318 IteratedCoefficientFrameEquivalence318
universe u
variable {X B Y T T' : Scheme.{u}} (p : X ⟶ B) (L : Line X) (q : Y ⟶ B)
  (E : AffineRelativeFrameClassifier318.Data p L q)
  (b : T ⟶ B) (b' : T' ⟶ B) (h : T' ⟶ T) (hh : h ≫ b=b')
abbrev coefficient := RelativeSchemeCoefficient318.map p b b' h hh
@[expose] def pullFrame (e : Frames (originalLine p L b)) : Frames (originalLine p L b') :=
  OriginalFramePathTransport318.transport L (coefficient p b b' h hh)
    (original p b) (original p b') (RelativeSchemeCoefficient318.map_fst _ _ _ _ _) e
variable (e : Frames (originalLine p L b)) (R : CommRingCat.{u}) (a : Spec R ⟶ T')
lemma test_base : (𝟙 (Spec R)) ≫ ((a ≫ h) ≫ b)=a ≫ b' := by
  rw [Category.id_comp,Category.assoc,hh]
abbrev testChange := RelativeSchemeCoefficient318.map p ((a ≫ h) ≫ b) (a ≫ b')
  (𝟙 (Spec R)) (test_base b b' h hh R a)
/-- Actual source-family transport commutes with the native full-frame
comparison, including the exact base reassociation on each affine test. -/
lemma frameAt_change :
    WholeFrameClassifyingRule318.frameAt p L b' (pullFrame p L b b' h hh e) R a=
    OriginalFramePathTransport318.transport L (testChange p b b' h hh R a)
      (pullback.fst p ((a ≫ h) ≫ b)) (pullback.fst p (a ≫ b'))
      (RelativeSchemeCoefficient318.map_fst _ _ _ _ _)
      (WholeFrameClassifyingRule318.frameAt p L b e R (a ≫ h)) := by
  unfold WholeFrameClassifyingRule318.frameAt
  rw [pullback_frame,pullback_frame]
  unfold pullFrame
  rw [OriginalFramePathTransport318.composition,OriginalFramePathTransport318.composition]
  apply OriginalFramePathTransport318.arrow_congr
  apply pullback.hom_ext
  · simp only [Category.assoc,RelativeSchemeCoefficient318.map_fst]
  · simp only [Category.assoc,RelativeSchemeCoefficient318.map_snd,
      RelativeSchemeCoefficient318.map_snd_assoc,Category.comp_id,Category.id_comp]
/-- The genuine whole-scheme classifying morphisms are natural for every
coefficient arrow. No affine, flat or reduced hypothesis is imposed on T,T'. -/
lemma classify :
    WholeFrameClassifyingRule318.classify p L q E b' (pullFrame p L b b' h hh e)=
      h ≫ WholeFrameClassifyingRule318.classify p L q E b e := by
  apply SchemeAffineMorphismEvaluation318.hom_ext
  intro R a
  rw [WholeFrameClassifyingRule318.test,←Category.assoc,WholeFrameClassifyingRule318.test]
  have hp : WholeFrameClassifyingRule318.localPoint p L q E b' (pullFrame p L b b' h hh e) R a=
      AffineRelativeFrameClassifier318.pointMap q R R (𝟙 (Spec R))
        ((a ≫ h) ≫ b) (a ≫ b') (test_base b b' h hh R a)
        (WholeFrameClassifyingRule318.localPoint p L q E b e R (a ≫ h)) := by
    apply (E.equivalence R (a ≫ b')).injective
    rw [WholeFrameClassifyingRule318.localPoint,Equiv.apply_symm_apply,←E.natural]
    rw [WholeFrameClassifyingRule318.localPoint,Equiv.apply_symm_apply]
    exact frameAt_change p L b b' h hh e R a
  have hv := congrArg Subtype.val hp
  simpa only [AffineRelativeFrameClassifier318.pointMap,Category.id_comp] using hv
end WholeFrameCoefficientNaturality318
