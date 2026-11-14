module
public import OriginalPulledCancellationComposition318
public import OriginalPulledDifferenceFrameWitness318
public section
noncomputable section
namespace OriginalInverseLineCancellationCoherence318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Line Z)
local notation "I" => FramedLineInverse318.inverse L
/-- Iterate the OLD left cancellation, retaining the pullback of the
old inverse I, rather than replacing it by an inverse chosen on Y. -/
@[expose] def iteratedLeft := OriginalPulledCancellationComposition318.pull f
  (LineSheafPullback318.line g I) (LineSheafPullback318.line g L)
  (OriginalPulledDifferenceFrameWitness318.leftCancel g L)
@[expose] def iteratedRight := OriginalPulledCancellationComposition318.pull f
  (LineSheafPullback318.line g L) (LineSheafPullback318.line g I)
  (OriginalPulledDifferenceFrameWitness318.rightCancel g L)
lemma left :
    TensorSheafFunctor318.congr ((Scheme.Modules.pullbackComp f g).app I.object)
      ((Scheme.Modules.pullbackComp f g).app L.object) ≪≫
      OriginalPulledDifferenceFrameWitness318.leftCancel (f ≫ g) L=iteratedLeft f g L :=
  OriginalPulledCancellationComposition318.composition f g I L (FramedLineInverse318.leftIso L)
lemma right :
    TensorSheafFunctor318.congr ((Scheme.Modules.pullbackComp f g).app L.object)
      ((Scheme.Modules.pullbackComp f g).app I.object) ≪≫
      OriginalPulledDifferenceFrameWitness318.rightCancel (f ≫ g) L=iteratedRight f g L :=
  OriginalPulledCancellationComposition318.composition f g L I (FramedLineInverse318.rightIso L)
end OriginalInverseLineCancellationCoherence318
