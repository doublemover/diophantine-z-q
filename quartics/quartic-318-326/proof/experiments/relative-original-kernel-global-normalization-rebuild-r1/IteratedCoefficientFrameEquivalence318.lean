module
public import OriginalNestedFrameFlatten318
public section
noncomputable section
namespace IteratedCoefficientFrameEquivalence318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open IteratedCoefficientFrameModel318
universe u
variable {X B S T : Scheme.{u}} (p : X ⟶ B) (L : Line X) (b : S ⟶ B) (a : T ⟶ S)
abbrev originalLine := LineSheafPullback318.line (original p b) L
abbrev nestedLine := LineSheafPullback318.line (inner p b a) (originalLine p L b)
abbrev directLine := LineSheafPullback318.line (pullback.fst p (a ≫ b)) L
@[expose] def flattened : Frames (LineSheafPullback318.line (composite p b a) L) ≃ Frames (directLine p L b a) :=
  (OriginalFrameIsoEquivalence318.equivalence (model p b a).hom
    (LineSheafPullback318.line (composite p b a) L)).trans
      (OriginalFrameIsoEquivalence318.target
        ((PullbackPathComposition318.iso (model p b a).hom (composite p b a)
          (pullback.fst p (a ≫ b)) (model_source p b a)).app L.object))
lemma flattened_forward (e : Frames (LineSheafPullback318.line (composite p b a) L)) :
    flattened p L b a e=OriginalFramePathTransport318.transport L (model p b a).hom
      (composite p b a) (pullback.fst p (a ≫ b)) (model_source p b a) e := rfl
/-- Genuine full-frame equivalence between the ACTUAL twice-pulled line
and the original canonical p-first family over the composite coefficient.
All four schemes are arbitrary; no affine, flat or reduced test assumption. -/
@[expose] def equivalence : Frames (nestedLine p L b a) ≃ Frames (directLine p L b a) :=
  (OriginalNestedFrameFlatten318.equivalence L (original p b) (inner p b a)).trans
    (flattened p L b a)
lemma forward (e : Frames (nestedLine p L b a)) : equivalence p L b a e=
    flattened p L b a (OriginalNestedFrameFlatten318.equivalence L (original p b) (inner p b a) e) := rfl
/-- On actual pullback frames the equivalence is the SAME original
coefficient transport, not a chosen bijection of frame sets. -/
lemma pullback_frame (e : Frames (originalLine p L b)) :
    equivalence p L b a (OriginalFramePullback318.frame (inner p b a) (originalLine p L b) e)=
      OriginalFramePathTransport318.transport L (coefficient p b a) (original p b)
        (pullback.fst p (a ≫ b)) (RelativeSchemeCoefficient318.map_fst _ _ _ _ _) e := by
  rw [forward,flattened_forward]
  change OriginalFramePathTransport318.transport L (model p b a).hom
    (composite p b a) (pullback.fst p (a ≫ b)) (model_source p b a)
    (OriginalFramePathTransport318.transport L (inner p b a) (original p b) (composite p b a) rfl e)=_
  rw [OriginalFramePathTransport318.composition]
  apply OriginalFramePathTransport318.arrow_congr
  exact model_inner p b a
end IteratedCoefficientFrameEquivalence318
