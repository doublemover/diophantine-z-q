module
public import OriginalFrameDescentData318
public import OriginalFrameCoverBaseChange318
public section
noncomputable section
namespace OriginalFrameDescentBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalFrameCoverSections318 OriginalFrameOverlapCompatibility318 OriginalFrameDescentData318
universe u
variable {X Z : Scheme.{u}} (L : Line X) {ι : Type u}
  (Y : ι → Scheme.{u}) (j : ∀ i,Y i ⟶ X) [∀ i,IsOpenImmersion (j i)]
  (hc : ⊤≤⨆i,(j i) ''ᵁ ⊤) (e : Data L Y j)
  (h : Z ⟶ X) (W : ι → Scheme.{u}) (k : ∀ i,W i ⟶ Z)
  [∀ i,IsOpenImmersion (k i)] (f : ∀ i,W i ⟶ Y i)
  (hf : ∀ i,f i ≫ j i=k i ≫ h)
local notation "N" => LineSheafPullback318.line h L
/-- The actual base-change frame on each cover member, with overlap
compatibility DERIVED from original effective descent and native squares. -/
@[expose] def map : Data N W k :=
  ⟨OriginalFrameCoverBaseChange318.localFrames L Y j e.val h W k f hf,
    (iff_compatible N W k _).mpr
      (OriginalFrameCoverBaseChange318.compatible L Y j hc e.val
        ((iff_compatible L Y j e.val).mp e.property) h W k f hf)⟩
lemma recover (hk : ⊤≤⨆i,(k i) ''ᵁ ⊤) :
    (equivalence N W k hk).symm (map L Y j hc e h W k f hf)=
    OriginalFramePullback318.frame h L ((equivalence L Y j hc).symm e) :=
  OriginalFrameCoverBaseChange318.frame_eq L Y j hc e.val
    ((iff_compatible L Y j e.val).mp e.property) h W k f hf hk
end OriginalFrameDescentBaseChange318
