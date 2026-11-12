module
public import PELOriginalEdgeEquality318
public import PELActualOriginalSideGluing318
public section
noncomputable section
namespace PELOriginalBoundaryAction318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELJointNormOneAction318
open PELDirichletOriginalUnits318 PELDirichletSidePairingData318 PELDirichletVertexCycles318
open PELOriginalVertexEquality318 PELOriginalEdgeEquality318
open PELRealProjectiveDifferential318 PELOriginalProjectiveTangents318
open PELRealKleinSideTransport318 PELActualOriginalSideGluing318
set_option maxHeartbeats 1800000

/-- Every acting unit is represented in the SAME complete original integer
order coordinates, with its original norm-one equation. -/
theorem actual_unit_coordinates (u : normOneUnits) :
    ∃ x : Coordinates, integerNorm x=1 ∧ embed x=((u.val:order):B) := by
  obtain ⟨x,hx⟩ := (show ((u.val:order):B)∈order from (u.val:order).property)
  refine ⟨x,?_,hx⟩
  have h := (mem_normOneUnits u.val).mp u.property
  rw [← hx,embed_norm] at h
  exact_mod_cast h

/-- Only the central sign is forgotten, and ONLY in the original base
coordinate action. This says nothing about its action on the abelian fiber. -/
theorem same_signed_base_action (u v : normOneUnits)
    (h : ((u.val:order):B)=((v.val:order):B) ∨
      ((u.val:order):B)= -((v.val:order):B)) (τ : HalfPlane) :
    u • τ=v • τ := by
  apply scaled_injective
  rw [original_unit_equivariance,original_unit_equivariance]
  rcases h with h | h
  · rw [h]
  · rw [h]
    unfold realMatrix
    rw [PELQuaternionKleinAction318.matrix_neg]

/-- Complete vertex classification now concerns the ORIGINAL upper-half-
plane action, not just a rational table map. The consumer may identify each
scaled point with its already constructed actual vertexPoint. -/
theorem original_vertex_action (u : normOneUnits) (v : Fin 28) (τ : HalfPlane)
    (hτ : (scaledFirst τ,scaledSecond τ)=realPoint (vertex v))
    (he : denominator (realMatrix ((u.val:order):B)) (realPoint (vertex v))=1) :
    ∃ w : Fin 28, vertexClass w=vertexClass v ∧
      (scaledFirst (u • τ),scaledSecond (u • τ))=realPoint (vertex w) := by
  obtain ⟨x,hn,hx⟩ := actual_unit_coordinates u
  have hrat : PELQuaternionKleinAction318.denominator (embed x) (vertex v)=1 := by
    rw [← hx,denominator_cast] at he
    exact_mod_cast he
  obtain ⟨w,hw,hact⟩ := every_vertex_equality v x hn hrat
  refine ⟨w,hw,?_⟩
  rw [original_unit_equivariance,hτ,← hx,action_cast,hact]

/-- The full equality-unit classification on an OPEN real side yields
exactly identity or its ORIGINAL side-pairing action on EVERY parameter.
No arbitrary group-generation or boundary-representative hypothesis. -/
theorem original_edge_action (u : normOneUnits) (e : Fin 28)
    (s : ℝ) (hs : 0<s) (hs1 : s<1)
    (he : denominator (realMatrix ((u.val:order):B))
      (realMix (realPoint (vertex (start e))) (realPoint (vertex (finish e))) s)=1)
    (τ : HalfPlane) : u • τ=τ ∨ u • τ=edgeUnit e • τ := by
  obtain ⟨x,hn,hx⟩ := actual_unit_coordinates u
  have he' : denominator (realMatrix (embed x))
      (realMix (realPoint (vertex (start e))) (realPoint (vertex (finish e))) s)=1 := by
    rw [hx]
    exact he
  have hc := every_real_edge_equality e x hn s hs hs1 he'
  have hone : embed (![1,0,0,0]:Coordinates)=(1:B) := by
    ext <;> norm_num [embed]
  have hneg : embed (![-1,0,0,0]:Coordinates)=(-1:B) := by
    ext <;> norm_num [embed]
  have hv : ((u.val:order):B)=(1:B) ∨ ((u.val:order):B)=(-1:B) ∨
      ((u.val:order):B)=embed (coefficients e) ∨
      ((u.val:order):B)= -embed (coefficients e) := by
    rw [← hx]
    rcases hc with h | h | h | h
    · exact Or.inl ((congrArg embed h).trans hone)
    · exact Or.inr (Or.inl ((congrArg embed h).trans hneg))
    · exact Or.inr (Or.inr (Or.inl (congrArg embed h)))
    · exact Or.inr (Or.inr (Or.inr ((congrArg embed h).trans (embed_neg _))))
  rcases hv with h | h | h | h
  · left
    simpa only [one_smul] using same_signed_base_action u 1 (Or.inl h) τ
  · left
    simpa only [one_smul] using same_signed_base_action u 1 (Or.inr h) τ
  · exact Or.inr (same_signed_base_action u (edgeUnit e) (Or.inl h) τ)
  · exact Or.inr (same_signed_base_action u (edgeUnit e) (Or.inr h) τ)
end PELOriginalBoundaryAction318
