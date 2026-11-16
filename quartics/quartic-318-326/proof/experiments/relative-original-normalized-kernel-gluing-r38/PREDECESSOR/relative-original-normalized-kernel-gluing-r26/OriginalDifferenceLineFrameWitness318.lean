module
public import ContactDifferenceAbsoluteRelation318
public import FramedLineInverse318
public import LineSheafTensorIsos318
public section
noncomputable section
namespace OriginalDifferenceLineFrameWitness318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineFrameUnitTorsor318
universe u
variable {X : Scheme.{u}} (L K : Line X)
/-- Literal tensor of the original inverse line with the other original
line. The inverse retains the original line's own full covering frames. -/
@[expose] def difference : Line X :=
  LineSheafTensor318.line (FramedLineInverse318.inverse L) K
@[expose] def frameOfIso (e : L.object ≅ K.object) : Frames (difference L K) :=
  (FramedLineInverse318.leftIso L).symm ≪≫
    TensorSheafFunctor318.congr (Iso.refl (FramedLineInverse318.inverse L).object) e
/-- Explicit actual line isomorphism from a full difference frame. No
bijection of Isom functors is asserted by these witness maps. -/
@[expose] def isoOfFrame (e : Frames (difference L K)) : L.object ≅ K.object :=
  (LineSheafTensorIsos318.rightUnit L).symm ≪≫
    TensorSheafFunctor318.congr (Iso.refl L.object) e ≪≫
    (LineSheafTensorIsos318.assoc L (FramedLineInverse318.inverse L) K).symm ≪≫
    TensorSheafFunctor318.congr (FramedLineInverse318.rightIso L) (Iso.refl K.object) ≪≫
    LineSheafTensorIsos318.leftUnit K
lemma nonempty_iff : Nonempty (Frames (difference L K)) ↔ Nonempty (L.object ≅ K.object) :=
  ⟨fun ⟨e⟩ => ⟨isoOfFrame L K e⟩,fun ⟨e⟩ => ⟨frameOfIso L K e⟩⟩
end OriginalDifferenceLineFrameWitness318
