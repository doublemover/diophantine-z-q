module
public import OriginalFrameOpenPath318
public section
noncomputable section
namespace OriginalFrameActualIntersections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open OriginalLineFrameUnitTorsor318 OriginalFrameCoverSections318
universe u
variable {X : Scheme.{u}} (L : Line X) {ι : Type u} (Y : ι → Scheme.{u})
  (j : ∀ i,Y i ⟶ X) [∀ i,IsOpenImmersion (j i)]
  (e : LocalFrames L Y j) (i k : ι)
abbrev intersection := pullback (j i) (j k)
abbrev into : intersection Y j i k ⟶ X := pullback.fst (j i) (j k) ≫ j i
lemma image : into Y j i k ''ᵁ ⊤=((j i) ''ᵁ ⊤) ⊓ ((j k) ''ᵁ ⊤) := by
  simp only [into,Scheme.Hom.image_top_eq_opensRange,Scheme.Hom.opensRange_comp,
    Scheme.Hom.opensRange_pullbackFst,Scheme.Hom.image_preimage_eq_opensRange_inf]
@[expose] def left : Frames (LineSheafPullback318.line (into Y j i k) L) :=
  OriginalFramePullback318.frame (pullback.fst (j i) (j k))
    (LineSheafPullback318.line (j i) L) (e i) ≪≫
      (PullbackPathComposition318.iso (pullback.fst (j i) (j k)) (j i)
        (into Y j i k) rfl).app L.object
@[expose] def right : Frames (LineSheafPullback318.line (into Y j i k) L) :=
  OriginalFramePullback318.frame (pullback.snd (j i) (j k))
    (LineSheafPullback318.line (j k) L) (e k) ≪≫
      (PullbackPathComposition318.iso (pullback.snd (j i) (j k)) (j k)
        (into Y j i k) pullback.condition.symm).app L.object
lemma left_value : OriginalOpenPullbackSections318.sectionsEquiv (into Y j i k) L.object
    ((left L Y j e i k).hom.app ⊤ 1)=
    L.object.presheaf.map (homOfLE (show into Y j i k ''ᵁ ⊤≤(j i) ''ᵁ ⊤ by
      rw [image]; exact inf_le_left)).op (pieces L Y j e i) :=
  OriginalFrameOpenPath318.value _ _ _ rfl L (e i)
lemma right_value : OriginalOpenPullbackSections318.sectionsEquiv (into Y j i k) L.object
    ((right L Y j e i k).hom.app ⊤ 1)=
    L.object.presheaf.map (homOfLE (show into Y j i k ''ᵁ ⊤≤(j k) ''ᵁ ⊤ by
      rw [image]; exact inf_le_right)).op (pieces L Y j e k) :=
  OriginalFrameOpenPath318.value _ _ _ pullback.condition.symm L (e k)
end OriginalFrameActualIntersections318
