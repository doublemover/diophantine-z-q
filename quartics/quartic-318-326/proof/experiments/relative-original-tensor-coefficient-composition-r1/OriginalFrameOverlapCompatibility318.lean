module
public import OriginalFrameActualIntersections318
public section
noncomputable section
namespace OriginalFrameOverlapCompatibility318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalFrameCoverSections318 OriginalFrameActualIntersections318
universe u
variable {X : Scheme.{u}} (L : Line X) {ι : Type u} (Y : ι → Scheme.{u})
  (j : ∀ i,Y i ⟶ X) [∀ i,IsOpenImmersion (j i)] (e : LocalFrames L Y j)
abbrev Overlap := ∀ i k,left L Y j e i k=right L Y j e i k
/-- Equality of the two actual pulled frames on each CATEGORICAL
intersection is equivalent to full ambient section compatibility. -/
lemma iff_compatible : Overlap L Y j e ↔ Compatible L Y j e := by
  constructor
  · intro h i k
    have hv := congrArg (fun a => OriginalOpenPullbackSections318.sectionsEquiv
      (into Y j i k) L.object (a.hom.app ⊤ 1)) (h i k)
    rw [left_value,right_value] at hv
    rw [←image Y j i k]
    exact hv
  · intro h i k
    apply Iso.ext
    apply ModuleTopExt318.ext
    apply (OriginalOpenPullbackSections318.sectionsEquiv (into Y j i k) L.object).injective
    rw [left_value,right_value]
    have hv := h i k
    rw [←image Y j i k] at hv
    exact hv
end OriginalFrameOverlapCompatibility318
