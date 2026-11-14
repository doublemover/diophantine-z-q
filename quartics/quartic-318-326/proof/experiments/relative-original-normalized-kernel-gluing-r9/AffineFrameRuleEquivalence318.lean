module
public import AffineFrameRuleRecovery318
public section
noncomputable section
namespace AffineFrameRuleEquivalence318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X : Scheme.{u}} (L : Line X)
lemma rule_ext {F G : AffineFrameRule318.Rule L}
    (h : ∀ (S : CommRingCat.{u}) (x : Spec S ⟶ X),F.app S x=G.app S x) : F=G := by
  cases F with
  | mk f hf =>
    cases G with
    | mk g hg =>
      have he : f=g := by funext S x; exact h S x
      cases he
      rfl
/-- Natural full-frame data on ALL affine test schemes are represented
by an actual global frame, with both inverse maps and every-test recovery.
This is a genuine sheaf-descent theorem, not an assumed representability interface. -/
@[expose] def equivalence : Frames L ≃ AffineFrameRule318.Rule L where
  toFun := AffineFrameRule318.ofFrame L
  invFun F := AffineFrameRuleGluing318.frame L F X.affineOpenCover
  left_inv e := AffineFrameRuleGluing318.ofFrame L X.affineOpenCover e
  right_inv F := by
    apply rule_ext L
    intro S x
    exact AffineFrameRuleRecovery318.evaluate L F X.affineOpenCover S x
lemma cover_independent (F : AffineFrameRule318.Rule L) (U V : X.AffineOpenCover) :
    AffineFrameRuleGluing318.frame L F U=AffineFrameRuleGluing318.frame L F V := by
  apply OriginalFrameCoverSections318.ext L (fun i => Spec (U.X i)) U.f
    (AffineFrameRuleGluing318.image_cover U)
  intro i
  change OriginalFramePullback318.frame (U.f i) L (AffineFrameRuleGluing318.frame L F U)=
    OriginalFramePullback318.frame (U.f i) L (AffineFrameRuleGluing318.frame L F V)
  rw [AffineFrameRuleRecovery318.evaluate,AffineFrameRuleRecovery318.evaluate]
end AffineFrameRuleEquivalence318
