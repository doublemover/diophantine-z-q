module
public import OriginalPulledDifferenceComposition318
public section
noncomputable section
namespace OriginalPulledDifferencePath318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
  (h : f ≫ g=k) (L K : Line Z)
@[expose] def pullIso
    (e : (LineSheafPullback318.line g L).object ≅ (LineSheafPullback318.line g K).object) :
    (LineSheafPullback318.line k L).object ≅ (LineSheafPullback318.line k K).object :=
  ((PullbackPathComposition318.iso f g k h).app L.object).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫ (PullbackPathComposition318.iso f g k h).app K.object
/-- Exact geometric coefficient-path transport of the specific original
full difference-frame map, with all native pullback comparisons retained. -/
lemma frameOfIso
    (e : (LineSheafPullback318.line g L).object ≅ (LineSheafPullback318.line g K).object) :
    OriginalFramePathTransport318.transport (OriginalDifferenceLineFrameWitness318.difference L K)
      f g k h (OriginalPulledDifferenceFrameWitness318.frameOfIso g L K e)=
    OriginalPulledDifferenceFrameWitness318.frameOfIso k L K (pullIso f g k h L K e) := by
  subst k
  simpa only [pullIso,OriginalPulledDifferenceComposition318.pullIso,
    OriginalFramePathTransport318.transport,PullbackPathComposition318.iso,
    Scheme.Modules.pullbackCongr,eqToIso_refl,Iso.trans_refl] using
    OriginalPulledDifferenceComposition318.frameOfIso f g L K e
end OriginalPulledDifferencePath318
