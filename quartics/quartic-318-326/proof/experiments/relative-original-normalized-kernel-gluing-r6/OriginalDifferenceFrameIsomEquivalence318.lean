module
public import OriginalTensorFrameMapEquivariance318
public import OriginalDifferenceLineFrameWitness318
public section
noncomputable section
namespace OriginalDifferenceFrameIsomEquivalence318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X : Scheme.{u}} (L K : Line X)
local notation "D" => OriginalDifferenceLineFrameWitness318.difference L K
/-- The specific original frameOfIso is now proved bijective. This does
NOT assert that the earlier independently constructed isoOfFrame is its inverse. -/
lemma bijective : Function.Bijective (OriginalDifferenceLineFrameWitness318.frameOfIso L K) := by
  have h := OriginalTensorFrameMapEquivariance318.bijective L K D
    (FramedLineInverse318.inverse L).object (FramedLineInverse318.leftIso L).symm
    (Iso.refl D.object) (OriginalDifferenceLineFrameWitness318.isoOfFrame L K)
  simpa only [OriginalTensorFrameMapEquivariance318.map,Iso.trans_refl,
    OriginalDifferenceLineFrameWitness318.frameOfIso] using h
@[expose] def equivalence : (L.object ≅ K.object) ≃ OriginalLineFrameUnitTorsor318.Frames D :=
  Equiv.ofBijective (OriginalDifferenceLineFrameWitness318.frameOfIso L K) (bijective L K)
lemma forward (e : L.object ≅ K.object) :
    equivalence L K e=OriginalDifferenceLineFrameWitness318.frameOfIso L K e := rfl
lemma frame_inverse (e : OriginalLineFrameUnitTorsor318.Frames D) :
    OriginalDifferenceLineFrameWitness318.frameOfIso L K ((equivalence L K).symm e)=e :=
  (equivalence L K).apply_symm_apply e
lemma isom_inverse (e : L.object ≅ K.object) :
    (equivalence L K).symm (OriginalDifferenceLineFrameWitness318.frameOfIso L K e)=e :=
  (equivalence L K).symm_apply_apply e
end OriginalDifferenceFrameIsomEquivalence318
