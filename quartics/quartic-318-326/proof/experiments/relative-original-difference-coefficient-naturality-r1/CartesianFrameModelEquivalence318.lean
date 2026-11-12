module
public import OriginalFrameIsoEquivalence318
public section
noncomputable section
namespace CartesianFrameModelEquivalence318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X Y B S : Scheme.{u}} (L : Line X) (f : Y ⟶ X) (r : Y ⟶ S)
  (p : X ⟶ B) (b : S ⟶ B) (H : IsPullback f r p b)
local notation "e" => H.isoPullback
@[expose] def comparison :
    (LineSheafPullback318.line e.hom (LineSheafPullback318.line (pullback.fst p b) L)).object ≅
      (LineSheafPullback318.line f L).object :=
  (PullbackPathComposition318.iso e.hom (pullback.fst p b) f H.isoPullback_hom_fst).app L.object
/-- The complete original Cartesian model and the canonical pullback
family classify the SAME full frames, with actual inverse functors. -/
@[expose] def equivalence : Frames (LineSheafPullback318.line (pullback.fst p b) L) ≃
    Frames (LineSheafPullback318.line f L) :=
  (OriginalFrameIsoEquivalence318.equivalence e.hom (LineSheafPullback318.line (pullback.fst p b) L)).trans
    (OriginalFrameIsoEquivalence318.target (comparison L f r p b H))
lemma forward (a : Frames (LineSheafPullback318.line (pullback.fst p b) L)) :
    equivalence L f r p b H a=OriginalFramePathTransport318.transport L e.hom
      (pullback.fst p b) f H.isoPullback_hom_fst a := rfl
end CartesianFrameModelEquivalence318
