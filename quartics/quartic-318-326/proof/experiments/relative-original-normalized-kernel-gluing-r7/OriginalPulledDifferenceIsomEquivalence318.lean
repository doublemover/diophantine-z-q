module
public import OriginalDifferenceFrameIsomEquivalence318
public import OriginalPulledDifferenceFrameWitness318
public section
noncomputable section
namespace OriginalPulledDifferenceIsomEquivalence318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) (L K : Line X)
local notation "A" => LineSheafPullback318.line f L
local notation "B" => LineSheafPullback318.line f K
local notation "I" => LineSheafPullback318.line f (FramedLineInverse318.inverse L)
local notation "D" => LineSheafPullback318.line f (OriginalDifferenceLineFrameWitness318.difference L K)
/-- The ACTUAL old pulled frame witness map is bijective on every whole
coefficient scheme. Native pulled cancellation and tensor comparisons are
retained, without identifying the pulled inverse with a freshly chosen one. -/
lemma bijective : Function.Bijective (OriginalPulledDifferenceFrameWitness318.frameOfIso f L K) :=
  OriginalTensorFrameMapEquivariance318.bijective A B D I.object
    (OriginalPulledDifferenceFrameWitness318.leftCancel f L).symm
    (LineClassPullbackHom318.tensorIso f (FramedLineInverse318.inverse L) K).symm
    (OriginalPulledDifferenceFrameWitness318.isoOfFrame f L K)
@[expose] def equivalence : (A.object ≅ B.object) ≃ OriginalLineFrameUnitTorsor318.Frames D :=
  Equiv.ofBijective (OriginalPulledDifferenceFrameWitness318.frameOfIso f L K) (bijective f L K)
lemma forward (e : A.object ≅ B.object) :
    equivalence f L K e=OriginalPulledDifferenceFrameWitness318.frameOfIso f L K e := rfl
lemma frame_inverse (e : OriginalLineFrameUnitTorsor318.Frames D) :
    OriginalPulledDifferenceFrameWitness318.frameOfIso f L K ((equivalence f L K).symm e)=e :=
  (equivalence f L K).apply_symm_apply e
lemma isom_inverse (e : A.object ≅ B.object) :
    (equivalence f L K).symm (OriginalPulledDifferenceFrameWitness318.frameOfIso f L K e)=e :=
  (equivalence f L K).symm_apply_apply e
end OriginalPulledDifferenceIsomEquivalence318
