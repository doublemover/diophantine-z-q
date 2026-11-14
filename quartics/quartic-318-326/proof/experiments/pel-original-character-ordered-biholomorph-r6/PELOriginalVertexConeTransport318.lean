module
public import RealOrientedCone318
public import PELOriginalSecondVertexRay318
public section
noncomputable section
namespace PELOriginalVertexConeTransport318
open PELDirichletSidePairingData318 PELDirichletVertexCycles318 PELDirichletVertexFan318
open PELOriginalProjectiveTangents318 PELOriginalVertexDerivatives318
open PELOriginalLocalCones318 PELOriginalRealFanCover318 PELOriginalSecondVertexRay318
open RealOrientedCone318
set_option maxHeartbeats 1800000

theorem original_edge_cross_positive (v : Fin 28) :
    0 < (orientation (vertexClass v):ℝ)*
      realCross (realPoint (secondDirection v)) (realPoint (sideDirection v)) := by
  fin_cases v <;> norm_num [orientation,vertexClass,realCross,realPoint,secondDirection,
    secondEndpoint,sideDirection,otherVertex,vertex]

theorem original_cone_span (v : Fin 28) (W : ℝ × ℝ) :
    W ∈ vertexCone v ↔ W ∈ rayCone (realPoint (secondDirection v)) (realPoint (sideDirection v)) :=
  (original_cone_cross_iff v W).trans
    (sector_iff_rayCone _ _ _ _ (original_edge_cross_positive v))

theorem actual_ray_cross_positive (v : Fin 28) :
    0 < (orientation (vertexClass (previousVertex v)):ℝ)*
      realCross (realPoint (ray (previousVertex v))) (realPoint (ray v)) := by
  have h := oriented_cross_positive (previousVertex v)
  rw [previous_next] at h
  have hreal : (0:ℝ) < (orientation (vertexClass (previousVertex v)):ℝ) *
      (cross (ray (previousVertex v)) (ray v):ℝ) := by exact_mod_cast h
  simpa [realCross,realPoint,cross] using hreal

/-- Exact full cone transport by the derivative of the ORIGINAL inverse
prefix. The cone is the PREVIOUS sector, not the outgoing sector v. -/
theorem actual_cone_transport (v : Fin 28) (W : ℝ × ℝ) :
    W ∈ vertexCone v ↔ sector (previousVertex v)
      (PELRealProjectiveDifferential318.differential
        (realMatrix (inversePrefix v)) (realPoint (vertex v)) W) := by
  rw [original_cone_span]
  rw [map_rayCone_iff _ (actual_fan_invertible v).1
    _ _ (realPoint (ray (previousVertex v))) (realPoint (ray v))
    (secondRayScale v:ℝ) (rayScale v:ℝ)
    (by exact_mod_cast secondScale_positive v) (by exact_mod_cast scale_positive v)
    (actual_second_tangent v) (actual_tangent_ray v)]
  change _ ↔ 0 ≤ _ * realCross _ _ ∧ 0 ≤ _ * realCross _ _
  rw [previous_next]
  exact (sector_iff_rayCone _ _ _ _ (actual_ray_cross_positive v)).symm
end PELOriginalVertexConeTransport318
