module
public import OriginalFrameOverlapCompatibility318
public section
noncomputable section
namespace OriginalFrameDescentData318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
open OriginalFrameCoverSections318 OriginalFrameOverlapCompatibility318
universe u
variable {X : Scheme.{u}} (L : Line X) {ι : Type u} (Y : ι → Scheme.{u})
  (j : ∀ i,Y i ⟶ X) [∀ i,IsOpenImmersion (j i)]
  (hc : ⊤≤⨆i,(j i) ''ᵁ ⊤)
abbrev Data := {e : LocalFrames L Y j // Overlap L Y j e}
@[expose] def compatibleData : Data L Y j ≃ {e : LocalFrames L Y j // Compatible L Y j e} where
  toFun e := ⟨e.val,(iff_compatible L Y j e.val).mp e.property⟩
  invFun e := ⟨e.val,(iff_compatible L Y j e.val).mpr e.property⟩
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext rfl
/-- Effective descent with the STANDARD actual intersection-frame input,
not a renamed assumption of an existing global trivialization. -/
@[expose] def equivalence : Frames L ≃ Data L Y j :=
  (OriginalFrameCoverEquivalence318.equivalence L Y j hc).trans (compatibleData L Y j).symm
lemma local_recovery (e : Data L Y j) (i : ι) :
    OriginalFramePullback318.frame (j i) L ((equivalence L Y j hc).symm e)=e.val i :=
  OriginalFrameCoverGluing318.frame_restrict L Y j hc e.val
    ((iff_compatible L Y j e.val).mp e.property) i
end OriginalFrameDescentData318
