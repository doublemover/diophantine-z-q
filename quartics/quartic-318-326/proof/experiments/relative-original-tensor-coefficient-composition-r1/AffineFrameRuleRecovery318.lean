module
public import AffineFramePreimageCover318
public section
noncomputable section
namespace AffineFrameRuleRecovery318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X : Scheme.{u}} (L : Line X) (F : AffineFrameRule318.Rule L) (U : X.AffineOpenCover)
  (S : CommRingCat.{u}) (x : Spec S ⟶ X)
local notation "e" => AffineFrameRuleGluing318.frame L F U
local notation "V" => AffineFramePreimageCover318.cover U S x
/-- The constructed global frame recovers the rule on EVERY affine
scheme test, not just cover inclusions. The true pulled cover and its
original square are used; no flatness or openness of x is assumed. -/
lemma evaluate : OriginalFramePullback318.frame x L e=F.app S x := by
  apply OriginalFrameCoverSections318.ext (LineSheafPullback318.line x L)
    (fun i => Spec (V.X i)) V.f (AffineFramePreimageCover318.image_cover U S x)
  intro i
  let a := AffineFramePreimageCover318.intoChart U S x i
  let y := V.f i
  have hs : a ≫ U.f i.1=y ≫ x := AffineFramePreimageCover318.square U S x i
  have hU := F.natural (U.X i.1) (V.X i) a (U.f i.1) (y ≫ x) hs
  rw [←AffineFrameRuleGluing318.on_chart L F U i.1] at hU
  have hQ := OriginalFramePullbackCoherence318.path a (U.f i.1) L (y ≫ x) hs e
  have hglobal : OriginalFramePullback318.frame (y ≫ x) L e=F.app (V.X i) (y ≫ x) :=
    hQ.symm.trans hU
  have hP := OriginalFramePullbackCoherence318.path y x L (y ≫ x) rfl e
  have hF := F.natural S (V.X i) y x (y ≫ x) rfl
  change OriginalFramePullback318.frame y (LineSheafPullback318.line x L)
    (OriginalFramePullback318.frame x L e)=
      OriginalFramePullback318.frame y (LineSheafPullback318.line x L) (F.app S x)
  apply Iso.ext
  apply (cancel_mono ((PullbackPathComposition318.iso y x (y ≫ x) rfl).app L.object).hom).mp
  exact congrArg Iso.hom ((hP.trans hglobal).trans hF.symm)
end AffineFrameRuleRecovery318
