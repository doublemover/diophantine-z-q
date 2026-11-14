module
public import AffineRelativeFrameClassifier318
public section
noncomputable section
namespace WholeFrameClassifyingRule318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open IteratedCoefficientFrameModel318 IteratedCoefficientFrameEquivalence318
universe u
variable {X B Y T : Scheme.{u}} (p : X ⟶ B) (L : Line X) (q : Y ⟶ B)
  (E : AffineRelativeFrameClassifier318.Data p L q) (b : T ⟶ B)
  (e : Frames (originalLine p L b))
@[expose] def frameAt (R : CommRingCat.{u}) (a : Spec R ⟶ T) : Frames (directLine p L b a) :=
  equivalence p L b a (OriginalFramePullback318.frame (inner p b a) (originalLine p L b) e)
lemma frameAt_natural (R S : CommRingCat.{u}) (g : Spec S ⟶ Spec R)
    (a : Spec R ⟶ T) (a' : Spec S ⟶ T) (hg : g ≫ a=a') :
    OriginalFramePathTransport318.transport L (directChange p b a a' g hg)
      (pullback.fst p (a ≫ b)) (pullback.fst p (a' ≫ b))
      (RelativeSchemeCoefficient318.map_fst _ _ _ _ _) (frameAt p L b e R a)=frameAt p L b e S a' := by
  rw [frameAt,←IteratedCoefficientFrameNaturality318.natural]
  rw [OriginalFramePullbackCoherence318.path]
  rfl
@[expose] def localPoint (R : CommRingCat.{u}) (a : Spec R ⟶ T) :
    AffineRelativeFrameClassifier318.Point q R (a ≫ b) :=
  (E.equivalence R (a ≫ b)).symm (frameAt p L b e R a)
@[expose] def rule : SchemeAffineMorphismRule318.Rule T Y where
  app R a := (localPoint p L q E b e R a).val
  natural R S g a a' hg := by
    change (localPoint p L q E b e S a').val=
      (AffineRelativeFrameClassifier318.pointMap q R S g (a ≫ b) (a' ≫ b)
        (by rw [←Category.assoc,hg]) (localPoint p L q E b e R a)).val
    apply congrArg Subtype.val
    apply (E.equivalence S (a' ≫ b)).injective
    rw [localPoint,Equiv.apply_symm_apply,←E.natural]
    rw [localPoint,Equiv.apply_symm_apply]
    exact (frameAt_natural p L b e R S g a a' hg).symm
/-- A genuine morphism on the original whole arbitrary coefficient scheme. -/
@[expose] def classify : T ⟶ Y := SchemeAffineMorphismRule318.realize (rule p L q E b e)
lemma test (R : CommRingCat.{u}) (a : Spec R ⟶ T) :
    a ≫ classify p L q E b e=(localPoint p L q E b e R a).val :=
  SchemeAffineMorphismEvaluation318.evaluate (rule p L q E b e) R a
lemma over : classify p L q E b e ≫ q=b := by
  apply SchemeAffineMorphismEvaluation318.hom_ext
  intro R a
  rw [←Category.assoc,test]
  exact (localPoint p L q E b e R a).property
end WholeFrameClassifyingRule318
