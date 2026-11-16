module
public import WholeFrameClassifyingRule318
public section
noncomputable section
namespace WholeParameterFrameRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open IteratedCoefficientFrameModel318 IteratedCoefficientFrameEquivalence318
universe u
variable {X B Y T : Scheme.{u}} (p : X ⟶ B) (L : Line X) (q : Y ⟶ B)
  (E : AffineRelativeFrameClassifier318.Data p L q) (b : T ⟶ B)
  (z : T ⟶ Y) (hz : z ≫ q=b)
@[expose] def localPoint (R : CommRingCat.{u}) (a : Spec R ⟶ T) :
    AffineRelativeFrameClassifier318.Point q R (a ≫ b) :=
  ⟨a ≫ z,by rw [Category.assoc,hz]⟩
/-- The parameter morphism produces an actual relative frame rule on
the original pulled line, not merely an isomorphism class. -/
@[expose] def rule : RelativeFamilyFrameRule318.Rule (projection p b) (originalLine p L b) where
  app R a := (equivalence p L b a).symm (E.equivalence R (a ≫ b) (localPoint q b z hz R a))
  natural R S g a a' hg := by
    apply (equivalence p L b a').injective
    rw [IteratedCoefficientFrameNaturality318.natural,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
    rw [E.natural]
    apply congrArg (E.equivalence S (a' ≫ b))
    apply Subtype.ext
    change g ≫ (a ≫ z)=a' ≫ z
    rw [←Category.assoc,hg]
@[expose] def recover : Frames (originalLine p L b) :=
  RelativeFamilyFrameRecovery318.frame (projection p b) (originalLine p L b) (rule p L q E b z hz)
/-- The recovered frame has exactly the prescribed full-family affine tests. -/
lemma test (R : CommRingCat.{u}) (a : Spec R ⟶ T) :
    equivalence p L b a (OriginalFramePullback318.frame (inner p b a) (originalLine p L b)
      (recover p L q E b z hz))=E.equivalence R (a ≫ b) (localPoint q b z hz R a) := by
  rw [recover,RelativeFamilyFrameRecovery318.family_test]
  exact (equivalence p L b a).apply_symm_apply _
end WholeParameterFrameRecovery318
