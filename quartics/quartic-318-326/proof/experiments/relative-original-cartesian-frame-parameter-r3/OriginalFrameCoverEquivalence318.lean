module
public import OriginalFrameCoverGluing318
public section
noncomputable section
namespace OriginalFrameCoverEquivalence318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
open OriginalFrameCoverSections318 OriginalFrameCoverGluing318
universe u
variable {X : Scheme.{u}} (L : Line X) {ι : Type u} (Y : ι → Scheme.{u})
  (j : ∀ i,Y i ⟶ X) [∀ i,IsOpenImmersion (j i)]
  (hc : ⊤≤⨆i,(j i) ''ᵁ ⊤)
/-- Effective descent of entire actual line trivializations, including
both inverse identities, on arbitrary open covers of arbitrary schemes. -/
@[expose] def equivalence : Frames L ≃ {e : LocalFrames L Y j // Compatible L Y j e} where
  toFun e := ⟨restrict L Y j e,restrict_compatible L Y j e⟩
  invFun e := frame L Y j hc e.val e.property
  left_inv e := by
    apply OriginalFrameCoverSections318.ext L Y j hc
    intro i
    exact frame_restrict L Y j hc _ _ i
  right_inv e := by
    apply Subtype.ext
    funext i
    exact frame_restrict L Y j hc e.val e.property i

lemma unique (e : LocalFrames L Y j) (he : Compatible L Y j e)
    (d : Frames L) (hd : ∀ i,restrict L Y j d i=e i) :
    d=frame L Y j hc e he := by
  apply OriginalFrameCoverSections318.ext L Y j hc
  intro i
  rw [frame_restrict]
  exact hd i
end OriginalFrameCoverEquivalence318
