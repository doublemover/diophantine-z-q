module
public import RelativeFamilyFrameGraphFactor318
public section
noncomputable section
namespace RelativeFamilyFrameRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X B : Scheme.{u}} (p : X ⟶ B) (L : Line X)
  (F : RelativeFamilyFrameRule318.Rule p L)
@[expose] def frame : Frames L :=
  (AffineFrameRuleEquivalence318.equivalence L).symm (RelativeFamilyFrameGraphNaturality318.rule p L F)
lemma source_test (S : CommRingCat.{u}) (x : Spec S ⟶ X) :
    OriginalFramePullback318.frame x L (frame p L F)=RelativeFamilyFrameGraph318.frame p L F S x :=
  AffineFrameRuleRecovery318.evaluate L (RelativeFamilyFrameGraphNaturality318.rule p L F)
    X.affineOpenCover S x
/-- Every actual affine BASE family, including non-flat and nonreduced
tests, recovers its entire original frame from the constructed global frame. -/
lemma family_test (S : CommRingCat.{u}) (b : Spec S ⟶ B) :
    OriginalFramePullback318.frame (pullback.fst p b) L (frame p L F)=F.app S b := by
  apply (AffineFrameRuleEquivalence318.equivalence (LineSheafPullback318.line (pullback.fst p b) L)).injective
  apply AffineFrameRuleEquivalence318.rule_ext
  intro T t
  change OriginalFramePullback318.frame t (LineSheafPullback318.line (pullback.fst p b) L)
    (OriginalFramePullback318.frame (pullback.fst p b) L (frame p L F))=
    OriginalFramePullback318.frame t (LineSheafPullback318.line (pullback.fst p b) L) (F.app S b)
  have h₁ := OriginalFramePullbackCoherence318.path t (pullback.fst p b) L
    (t ≫ pullback.fst p b) rfl (frame p L F)
  have h₂ := source_test p L F T (t ≫ pullback.fst p b)
  have h₃ := RelativeFamilyFrameGraphFactor318.frame_eq p L F S T b t
  apply Iso.ext
  apply (cancel_mono ((PullbackPathComposition318.iso t (pullback.fst p b)
    (t ≫ pullback.fst p b) rfl).app L.object).hom).mp
  exact congrArg Iso.hom ((h₁.trans h₂).trans h₃)
lemma ofFrame (e : Frames L) : frame p L (RelativeFamilyFrameRule318.ofFrame p L e)=e := by
  apply (AffineFrameRuleEquivalence318.equivalence L).injective
  apply AffineFrameRuleEquivalence318.rule_ext
  intro S x
  change OriginalFramePullback318.frame x L (frame p L (RelativeFamilyFrameRule318.ofFrame p L e))=
    OriginalFramePullback318.frame x L e
  rw [source_test]
  exact OriginalFramePullbackCoherence318.path (RelativeFamilyFrameGraph318.graph p S x)
    (pullback.fst p (x ≫ p)) L x (RelativeFamilyFrameGraph318.graph_fst p S x) e
end RelativeFamilyFrameRecovery318
