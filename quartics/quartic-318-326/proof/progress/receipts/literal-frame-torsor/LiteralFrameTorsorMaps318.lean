module
public import LiteralGeometricFrameTransitivity318
public import LiteralIndependentPairRank318
public section
noncomputable section
namespace LiteralFrameTorsorMaps318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
abbrev Frame:=LiteralIndependentPairOpen318.scheme N
abbrev base:=LiteralIndependentPairFinite318.structureMap N
@[expose] def family:=pullback (base N) (base N)
@[expose] def projection : family N ⟶ Frame N:=pullback.fst _ _
@[expose] def second : family N ⟶ Frame N:=pullback.snd _ _
local instance : Etale (base N):=(LiteralIndependentPairFinite318.finite_etale N).2
instance projection_etale : Etale (projection N):=by
  dsimp only [projection,family]
  infer_instance
/-- The g-th graph is the actual graph x -> (x,x.g) over the literal base. -/
@[expose] def graph (g:F3FrameChange318.Group) : Frame N ⟶ family N:=
  pullback.lift (𝟙 _) (LiteralIndependentFrameChange318.map N g) (by
    rw [Category.id_comp,LiteralIndependentSectionAction318.map_structure])
@[reassoc] theorem graph_projection (g:F3FrameChange318.Group) : graph N g ≫ projection N=𝟙 _:=by
  simp [graph,projection]
@[reassoc] theorem graph_second (g:F3FrameChange318.Group) :
    graph N g ≫ second N=LiteralIndependentFrameChange318.map N g:=by
  simp [graph,second]
end LiteralFrameTorsorMaps318
