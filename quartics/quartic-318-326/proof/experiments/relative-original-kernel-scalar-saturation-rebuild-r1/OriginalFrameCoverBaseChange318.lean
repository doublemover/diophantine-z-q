module
public import OriginalFrameCoverEquivalence318
public section
noncomputable section
namespace OriginalFrameCoverBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
open OriginalFrameCoverSections318 OriginalFrameCoverGluing318
universe u
variable {X Z : Scheme.{u}} (L : Line X) {ι : Type u}
  (Y : ι → Scheme.{u}) (j : ∀ i,Y i ⟶ X) [∀ i,IsOpenImmersion (j i)]
  (hc : ⊤≤⨆i,(j i) ''ᵁ ⊤) (e : LocalFrames L Y j) (he : Compatible L Y j e)
  (h : Z ⟶ X) (W : ι → Scheme.{u}) (k : ∀ i,W i ⟶ Z)
  [∀ i,IsOpenImmersion (k i)] (f : ∀ i,W i ⟶ Y i)
  (hf : ∀ i,f i ≫ j i=k i ≫ h)
local notation "N" => LineSheafPullback318.line h L
/-- Actual local base change, with its original geometric-square iso. -/
@[expose] def localFrames : LocalFrames N W k := fun i =>
  OriginalFramePullback318.frame (f i) (LineSheafPullback318.line (j i) L) (e i) ≪≫
    OriginalFramePullbackCoherence318.squareIso (f i) (j i) L (k i) h (hf i)
lemma local_eq (i : ι) : localFrames L Y j e h W k f hf i=
    restrict N W k (OriginalFramePullback318.frame h L (frame L Y j hc e he)) i := by
  rw [localFrames,←frame_restrict L Y j hc e he i]
  exact OriginalFramePullbackCoherence318.square (f i) (j i) L (k i) h (hf i)
    (frame L Y j hc e he)
include hc he in
lemma compatible : Compatible N W k (localFrames L Y j e h W k f hf) := by
  have hh : localFrames L Y j e h W k f hf=
      restrict N W k (OriginalFramePullback318.frame h L (frame L Y j hc e he)) := by
    funext i
    exact local_eq L Y j hc e he h W k f hf i
  rw [hh]
  exact restrict_compatible N W k _
/-- Effectiveness of whole-frame descent commutes with arbitrary base
change. Flatness is not required; only the displayed actual cover and square. -/
lemma frame_eq (hk : ⊤≤⨆i,(k i) ''ᵁ ⊤) :
    frame N W k hk (localFrames L Y j e h W k f hf)
      (compatible L Y j hc e he h W k f hf)=
    OriginalFramePullback318.frame h L (frame L Y j hc e he) := by
  apply OriginalFrameCoverSections318.ext N W k hk
  intro i
  rw [frame_restrict]
  exact local_eq L Y j hc e he h W k f hf i
end OriginalFrameCoverBaseChange318
