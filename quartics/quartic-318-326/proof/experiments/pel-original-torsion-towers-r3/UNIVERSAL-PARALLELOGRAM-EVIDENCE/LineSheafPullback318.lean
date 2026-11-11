module
public import LinePullbackFrames318
public import LineSheafClass318
public section
noncomputable section
namespace LineSheafPullback318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y)
/-- The unchanged actual Scheme.Modules.pullback, with genuine frames on
whole inverse images of the original target line's covering opens. -/
@[expose] def line (L:Line Y):Line X where
  object:=(Scheme.Modules.pullback f).obj L.object
  Index:=L.Index
  opens:=fun i=>f⁻¹ᵁL.opens i
  cover:=LinePullbackFrames318.preimage_cover f L.opens L.cover
  frame:=fun i=>LinePullbackFrames318.frame f L.object (L.opens i) (L.frame i)
@[expose] def congr {L N:Line Y} (e:L.object≅N.object):
    (line f L).object≅(line f N).object:=(Scheme.Modules.pullback f).mapIso e
lemma respects {L N:Line Y} (h:Related L N):Related (line f L) (line f N):=by
  obtain ⟨e⟩:=h
  exact ⟨congr f e⟩
/-- Actual module-sheaf pullback on original line isomorphism classes.
The transition-function comparison remains a distinct subsequent theorem. -/
@[expose] def pullback:Class Y→Class X:=Quotient.map (line f) (fun _ _ h=>respects f h)
lemma pullback_classOf (L:Line Y):pullback f (classOf L)=classOf (line f L):=rfl
lemma presentation_independent {L N:Line Y} (e:L.object≅N.object):
    pullback f (classOf L)=pullback f (classOf N):=classOf_eq (congr f e)
end LineSheafPullback318
