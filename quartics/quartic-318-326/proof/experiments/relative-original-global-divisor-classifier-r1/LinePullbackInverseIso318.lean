module
public import InverseImageInverseCocycle318
public import LinePullbackTransitions318
public import LineSheafPullback318
public import FramedLineInverse318
public import LineSheafClassGroup318
public section
noncomputable section
namespace LinePullbackInverseIso318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Line Y)
local notation "I" => FramedLineInverse318.inverse L
local notation "P" => LineSheafPullback318.line f L
local notation "Q" => LineSheafPullback318.line f I
local notation "J" => FramedLineInverse318.inverse P

lemma pushed_cocycle :
    InverseImageLineCocycle318.cocycle f Q.object L.opens Q.frame=
      InverseImageLineCocycle318.cocycle f J.object L.opens J.frame := by
  rw [LinePullbackTransitions318.cocycle,
    LineSheafInverse318.original_inverse_transitions,UnitCocycleInverse318.map_inverse]
  rw [← LinePullbackTransitions318.cocycle]
  exact (InverseImageInverseCocycle318.inverse f P.object L.opens P.frame).symm

lemma cocycle : LineFrameCocycle318.cocycle Q.object Q.opens Q.frame=
    LineFrameCocycle318.cocycle J.object J.opens J.frame := by
  apply UnitTransitionCocycle318.Cocycle.ext
  intro i j
  exact congrArg (fun q => q.transition i j) (pushed_cocycle f L)

/-- Actual inverse-line pullback compatibility, reconstructed from the
ORIGINAL full-overlap transition equality and genuine covering frames. -/
@[expose] def iso : Q.object ≅ J.object :=
  CocycleEqualityTransport318.changeTarget Q.opens
    (LineFrameReconstructionIso318.iso Q.object Q.opens Q.frame Q.cover) (cocycle f L) ≪≫
  (LineFrameReconstructionIso318.iso J.object J.opens J.frame J.cover).symm

lemma class_inverse :
    LineSheafPullback318.pullback f (classOf (FramedLineInverse318.inverse L))=
      (LineSheafPullback318.pullback f (classOf L))⁻¹ := by
  calc
    _ = classOf J := LineSheafClass318.classOf_eq (iso f L)
    _ = _ := LineSheafClassGroup318.classOf_inverse P
end LinePullbackInverseIso318
