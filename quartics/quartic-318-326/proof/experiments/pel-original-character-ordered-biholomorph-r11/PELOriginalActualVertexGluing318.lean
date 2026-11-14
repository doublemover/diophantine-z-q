module
public import PELOriginalPolygonStratification318
public section
noncomputable section
namespace PELOriginalActualVertexGluing318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELDirichletSidePairingData318 PELDirichletVertexCycles318
open PELOriginalDirichletPolygon318 PELActualPolygonHomeomorph318
open PELOriginalProjectiveTangents318 PELActualOriginalSideGluing318
open PELOriginalSideQuotient318 PELOriginalPolygonStratification318
open PELStrictPolygonExtension318
set_option maxHeartbeats 1800000

@[expose] def vertexPoint (v : Fin 28) : originalDomain :=
  polygonInverse ⟨realPoint (vertex v),vertex_in_polygon v⟩

theorem vertexPoint_coordinates (v : Fin 28) :
    (scaledFirst (vertexPoint v).val,scaledSecond (vertexPoint v).val)=realPoint (vertex v) :=
  Prod.ext (inverse_scaled _).1 (inverse_scaled _).2

theorem segment_zero (v w : Fin 28) :
    segmentPoint v w 0 (by norm_num) (by norm_num)=vertexPoint v := by
  apply Subtype.ext
  apply scaled_injective
  rw [segment_coordinates,vertexPoint_coordinates]
  simp [PELRealKleinSideTransport318.realMix]

theorem segment_one (v w : Fin 28) :
    segmentPoint v w 1 (by norm_num) (by norm_num)=vertexPoint w := by
  apply Subtype.ext
  apply scaled_injective
  rw [segment_coordinates,vertexPoint_coordinates]
  simp [PELRealKleinSideTransport318.realMix]

/-- Endpoint graph steps are now actual equalities in the ORIGINAL compact
polygon quotient, using genuine whole-side gluing rather than graph labels. -/
theorem endpointStep_quotient {a b : Fin 28} (h : EndpointStep a b) :
    polygonProjection (vertexPoint a)=polygonProjection (vertexPoint b) := by
  obtain ⟨e,h|h⟩ := h
  · obtain ⟨rfl,rfl⟩ := h
    simpa only [segment_zero] using original_paired_side e 0 (by norm_num) (by norm_num)
  · obtain ⟨rfl,rfl⟩ := h
    simpa only [segment_one] using original_paired_side e 1 (by norm_num) (by norm_num)

theorem endpointPath_quotient {a b : Fin 28} (h : Path a b) :
    polygonProjection (vertexPoint a)=polygonProjection (vertexPoint b) := by
  induction h with
  | refl a => rfl
  | extend h hs ih => exact ih.trans (endpointStep_quotient hs)

theorem same_class_quotient (a b : Fin 28) (h : vertexClass a=vertexClass b) :
    polygonProjection (vertexPoint a)=polygonProjection (vertexPoint b) :=
  endpointPath_quotient ((path_iff_class a b).mpr h)

/-- The full finite polygon stratification transported back to the ACTUAL
upper-half-plane representatives; no hypothetical cell complex is consumed. -/
theorem original_point_stratification (τ : HalfPlane) (hτ : τ∈originalDomain) :
    strictInequalities (scaledFirst τ) (scaledSecond τ) ∨
      (∃ v : Fin 28, τ=(vertexPoint v).val) ∨
      ∃ (e : Fin 28) (s : ℝ) (hs0 : 0<s) (hs1 : s<1),
        τ=(segmentPoint (start e) (finish e) s hs0.le hs1.le).val := by
  rcases actual_plane_stratification (scaledFirst τ,scaledSecond τ) hτ with
    hs | ⟨v,hv⟩ | ⟨e,s,hs0,hs1,he⟩
  · exact Or.inl hs
  · right; left
    refine ⟨v,scaled_injective ?_⟩
    exact hv.trans (vertexPoint_coordinates v).symm
  · right; right
    refine ⟨e,s,hs0,hs1,scaled_injective ?_⟩
    exact he.trans (segment_coordinates _ _ _ _ _).symm
end PELOriginalActualVertexGluing318
