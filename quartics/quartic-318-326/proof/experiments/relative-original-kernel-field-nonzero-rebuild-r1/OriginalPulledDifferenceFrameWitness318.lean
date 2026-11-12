module
public import OriginalDifferenceLineFrameWitness318
public section
noncomputable section
namespace OriginalPulledDifferenceFrameWitness318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) (L K : Line X)
local notation "D" => FramedLineInverse318.inverse L
local notation "A" => LineSheafPullback318.line f L
local notation "B" => LineSheafPullback318.line f K
local notation "I" => LineSheafPullback318.line f D
/-- Pull the actual original cancellation through the exact native
tensor comparison. No identification with a freshly chosen inverse is assumed. -/
@[expose] def rightCancel : (LineSheafTensor318.line A I).object ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (LineClassPullbackHom318.tensorIso f L D).symm ≪≫
    (Scheme.Modules.pullback f).mapIso (FramedLineInverse318.rightIso L) ≪≫
    IdentityCotangent318.pullbackUnitIso f
@[expose] def leftCancel : (LineSheafTensor318.line I A).object ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (LineClassPullbackHom318.tensorIso f D L).symm ≪≫
    (Scheme.Modules.pullback f).mapIso (FramedLineInverse318.leftIso L) ≪≫
    IdentityCotangent318.pullbackUnitIso f
@[expose] def frameOfIso (e : A.object ≅ B.object) :
    Frames (LineSheafPullback318.line f (OriginalDifferenceLineFrameWitness318.difference L K)) :=
  (leftCancel f L).symm ≪≫ TensorSheafFunctor318.congr (Iso.refl I.object) e ≪≫
    (LineClassPullbackHom318.tensorIso f D K).symm
@[expose] def isoOfFrame
    (e : Frames (LineSheafPullback318.line f (OriginalDifferenceLineFrameWitness318.difference L K))) :
    A.object ≅ B.object :=
  (LineSheafTensorIsos318.rightUnit A).symm ≪≫
    TensorSheafFunctor318.congr (Iso.refl A.object) (e ≪≫ LineClassPullbackHom318.tensorIso f D K) ≪≫
    (LineSheafTensorIsos318.assoc A I B).symm ≪≫
    TensorSheafFunctor318.congr (rightCancel f L) (Iso.refl B.object) ≪≫
    LineSheafTensorIsos318.leftUnit B
/-- Exact relation on arbitrary whole coefficient pullbacks. The two
witness constructions need no unproved inverse-line pullback coherence. -/
lemma nonempty_iff :
    Nonempty (Frames (LineSheafPullback318.line f (OriginalDifferenceLineFrameWitness318.difference L K))) ↔
      Nonempty (A.object ≅ B.object) :=
  ⟨fun ⟨e⟩ => ⟨isoOfFrame f L K e⟩,fun ⟨e⟩ => ⟨frameOfIso f L K e⟩⟩
end OriginalPulledDifferenceFrameWitness318
