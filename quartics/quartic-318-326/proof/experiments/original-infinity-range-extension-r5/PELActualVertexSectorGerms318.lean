module
public import PELOriginalVertexConeTransport318
public section
noncomputable section
namespace PELActualVertexSectorGerms318
open PELRealProjectiveDifferential318
open PELOriginalLocalCones318 PELOriginalRealFanCover318 PELOriginalSecondVertexRay318
open PELOriginalProjectiveTangents318 PELOriginalVertexDerivatives318
open PELOriginalVertexConeTransport318 PELDirichletSidePairingData318
open PELOriginalDirichletPolygon318
set_option maxHeartbeats 1800000

/-- Exact projective displacement is a POSITIVE radial rescaling of the
actual derivative whenever both homogeneous denominators are positive. -/
theorem projective_displacement (M : HomogeneousMatrix) (P Q : ℝ × ℝ)
    (hP : denominator M P ≠ 0) (hQ : denominator M Q ≠ 0) :
    realAction M Q-realAction M P =
      (denominator M P/denominator M Q) • differential M P (Q-P) := by
  apply Prod.ext
  · change (M *ᵥ ![Q.1,Q.2,1]) 0/denominator M Q-
      (M *ᵥ ![P.1,P.2,1]) 0/denominator M P=
      (denominator M P/denominator M Q)*quotientRow M P 0 (Q-P)
    rw [quotientRow_apply M P (Q-P) hP]
    field_simp [hP,hQ]
    simp only [denominator,affineForm,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,mul_one]
    ring
  · change (M *ᵥ ![Q.1,Q.2,1]) 1/denominator M Q-
      (M *ᵥ ![P.1,P.2,1]) 1/denominator M P=
      (denominator M P/denominator M Q)*quotientRow M P 1 (Q-P)
    rw [quotientRow_apply M P (Q-P) hP]
    field_simp [hP,hQ]
    simp only [denominator,affineForm,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,mul_one]
    ring

theorem sector_positive_smul (v : Fin 28) (c : ℝ) (hc : 0<c) (W : ℝ × ℝ) :
    sector v (c • W) ↔ sector v W := by
  unfold sector
  have h1 : (PELDirichletVertexFan318.orientation (PELDirichletVertexCycles318.vertexClass v):ℝ)*
      realCross (realPoint (PELDirichletVertexFan318.ray v)) (c • W)=
      c*((PELDirichletVertexFan318.orientation (PELDirichletVertexCycles318.vertexClass v):ℝ)*
        realCross (realPoint (PELDirichletVertexFan318.ray v)) W) := by
    simp [realCross,realPoint]
    ring
  have h2 : (PELDirichletVertexFan318.orientation (PELDirichletVertexCycles318.vertexClass v):ℝ)*
      realCross (c • W) (realPoint (PELDirichletVertexFan318.ray (PELDirichletVertexCycles318.nextVertex v)))=
      c*((PELDirichletVertexFan318.orientation (PELDirichletVertexCycles318.vertexClass v):ℝ)*
        realCross W (realPoint (PELDirichletVertexFan318.ray (PELDirichletVertexCycles318.nextVertex v)))) := by
    simp [realCross,realPoint]
    ring
  rw [h1,h2,mul_nonneg_iff_of_pos_left hc,mul_nonneg_iff_of_pos_left hc]

theorem denominator_continuous (M : HomogeneousMatrix) : Continuous (denominator M) := by
  simp only [denominator,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  fun_prop

/-- The actual nonlinear original projective map, not only its derivative,
identifies the germ of the literal polygon at v with its PREVIOUS sector.
No quotient local disk, injectivity of the arithmetic comparison or global
fundamental-polygon conclusion is supplied here. -/
theorem original_vertex_sector_germ (v : Fin 28) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ realPoint (vertex v) ∈ U ∧
      ∀ Q ∈ U, Q ∈ planePolygon ↔ sector (previousVertex v)
        (realAction (realMatrix (inversePrefix v)) Q-
         realAction (realMatrix (inversePrefix v)) (realPoint (vertex v))) := by
  obtain ⟨U,hU,hv,hlocal⟩ := actual_vertex_cone_neighborhood v
  let M := realMatrix (inversePrefix v)
  let P := realPoint (vertex v)
  have hp : 0<denominator M P := real_denominator_positive v
  refine ⟨U ∩ {Q | 0<denominator M Q},hU.inter (isOpen_lt continuous_const
    (denominator_continuous M)),⟨hv,hp⟩,?_⟩
  intro Q hQ
  rw [hlocal Q hQ.1,actual_cone_transport]
  rw [projective_displacement M P Q hp.ne' hQ.2.ne']
  exact (sector_positive_smul _ _ (div_pos hp hQ.2) _).symm
end PELActualVertexSectorGerms318
