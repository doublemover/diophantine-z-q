module
public import OriginalFrameCoverEquivalence318
public section
noncomputable section
namespace OriginalFrameOpenPath318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
  [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion k]
  (h : f ≫ g=k) (L : Line Z) (e : Frames (LineSheafPullback318.line g L))
/-- Whole ambient restriction of a local frame agrees with its genuine
pulled frame along an actual open path, including the module associator. -/
lemma value : OriginalOpenPullbackSections318.sectionsEquiv k L.object
    ((OriginalFramePullback318.frame f (LineSheafPullback318.line g L) e ≪≫
      (PullbackPathComposition318.iso f g k h).app L.object).hom.app ⊤ 1)=
    L.object.presheaf.map (homOfLE (show k ''ᵁ ⊤≤g ''ᵁ ⊤ by
      rw [←h]; exact OpenChartSections318.imageLE f g)).op
      (OriginalOpenPullbackSections318.sectionsEquiv g L.object (e.hom.app ⊤ 1)) := by
  change OriginalOpenPullbackSections318.sectionsEquiv k L.object
    (((PullbackPathComposition318.iso f g k h).hom.app L.object).app ⊤
      ((OriginalFramePullback318.frame f (LineSheafPullback318.line g L) e).hom.app ⊤ 1))=_
  rw [OriginalFramePullback318.value]
  exact OriginalOpenPullbackSections318.nested_path f g k h L.object (e.hom.app ⊤ 1)
end OriginalFrameOpenPath318
