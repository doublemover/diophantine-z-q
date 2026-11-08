module
public import LiteralFrameTorsorGeometric318
public section
noncomputable section
namespace LiteralFrameTorsor318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralFrameTorsorMaps318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) [NeZero N]
/-- Actual GL2 torsor comparison. Its g-th component is exactly
x -> (x,x.g), and the inverse is the inverse of the actual disjoint-open
gluing isomorphism. This is stronger than a geometric cardinality claim. -/
@[expose] def iso : (∐ fun _ : F3FrameChange318.Group=>Frame N) ≅ family N:=
  EtaleSectionTrivialization318.iso (projection N) (graph N) (graph_projection N)
    (LiteralFrameTorsorGeometric318.all_geometric N)
@[reassoc] theorem component (g:F3FrameChange318.Group) :
    Sigma.ι (fun _ : F3FrameChange318.Group=>Frame N) g ≫ (iso N).hom=graph N g:=
  EtaleSectionTrivialization318.component _ _ _ _ g
@[reassoc] theorem component_first (g:F3FrameChange318.Group) :
    Sigma.ι (fun _ : F3FrameChange318.Group=>Frame N) g ≫ (iso N).hom ≫ projection N=𝟙 _:=by
  rw [component_assoc,graph_projection]
@[reassoc] theorem component_second (g:F3FrameChange318.Group) :
    Sigma.ι (fun _ : F3FrameChange318.Group=>Frame N) g ≫ (iso N).hom ≫ second N=
    LiteralIndependentFrameChange318.map N g:=by
  rw [component_assoc,graph_second]
@[reassoc] theorem graph_inverse (g:F3FrameChange318.Group) :
    graph N g ≫ (iso N).inv=Sigma.ι (fun _ : F3FrameChange318.Group=>Frame N) g:=by
  rw [←component N g,Category.assoc,Iso.hom_inv_id,Category.comp_id]
@[reassoc] theorem over_frame : (iso N).hom ≫ projection N=
    Sigma.desc (fun _ : F3FrameChange318.Group=>𝟙 (Frame N)):=
  EtaleSectionTrivialization318.base _ _ _ _
/-- The acted-on Scheme is the existing finite-etale surjective cover. -/
theorem cover : IsFinite (base N) ∧ Etale (base N) ∧ Surjective (base N):=
  LiteralIndependentPairRank318.finite_etale_surjective N
end LiteralFrameTorsor318
