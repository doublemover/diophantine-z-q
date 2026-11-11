module
public import AffineFrameRuleCompatibility318
public section
noncomputable section
namespace AffineFrameRuleGluing318
open AlgebraicGeometry CategoryTheory TopologicalSpace LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X : Scheme.{u}} (L : Line X) (F : AffineFrameRule318.Rule L)
  (U : X.AffineOpenCover)
lemma image_cover : ⊤≤⨆i,U.f i ''ᵁ ⊤ := by
  intro x _
  obtain ⟨i,y,hy⟩ := U.openCover.exists_eq x
  exact Opens.mem_iSup.mpr ⟨i,y,trivial,hy⟩
/-- A natural rule on all affine tests produces a genuine original
whole frame by effective full-cover descent, without a global frame premise. -/
@[expose] def frame : Frames L :=
  OriginalFrameCoverGluing318.frame L (fun i => Spec (U.X i)) U.f (image_cover U)
    (AffineFrameRuleCompatibility318.localFrames L F U)
    (AffineFrameRuleCompatibility318.compatible L F U)
lemma on_chart (i : U.I₀) : OriginalFramePullback318.frame (U.f i) L (frame L F U)=F.app (U.X i) (U.f i) :=
  OriginalFrameCoverGluing318.frame_restrict L (fun i => Spec (U.X i)) U.f (image_cover U)
    (AffineFrameRuleCompatibility318.localFrames L F U)
    (AffineFrameRuleCompatibility318.compatible L F U) i
/-- Existing actual frames are recovered exactly, including their entire
forward and inverse maps. -/
lemma ofFrame (e : Frames L) : frame L (AffineFrameRule318.ofFrame L e) U=e := by
  apply OriginalFrameCoverSections318.ext L (fun i => Spec (U.X i)) U.f (image_cover U)
  intro i
  exact on_chart L (AffineFrameRule318.ofFrame L e) U i
end AffineFrameRuleGluing318
