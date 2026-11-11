module
public import PELRealKleinSideTransport318
public import PELDirichletIncidence318
public import PELOriginalSideQuotient318
public section
noncomputable section
namespace PELActualOriginalSideGluing318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318 PELDirichletOriginalUnits318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELDirichletSidePairingData318
open PELDirichletIncidence318 PELOriginalDirichletPolygon318 PELActualPolygonHomeomorph318
open PELOriginalKleinHomeomorph318 PELRealKleinSideTransport318 PELOriginalSideQuotient318
open PELRealProjectiveDifferential318 PELOriginalProjectiveTangents318
open PELQuaternionRealRepresentation318
set_option maxHeartbeats 1800000

theorem vertex_in_polygon (v : Fin 28) : realPoint (vertex v)∈planePolygon := by
  intro j ε δ
  have h : (rowFirst j:ℝ)*(sign ε:ℝ)*((vertex v).1:ℝ)+
      (rowSecond j:ℝ)*(sign δ:ℝ)*((vertex v).2:ℝ)≤(rowConstant j:ℝ) := by
    exact_mod_cast vertex_all_signed_rows v j ε δ
  simpa only [realPoint,mul_assoc] using h

theorem realMix_in_polygon (P Q : ℝ×ℝ) (hP : P∈planePolygon) (hQ : Q∈planePolygon)
    (s : ℝ) (hs0 : 0≤s) (hs1 : s≤1) : realMix P Q s∈planePolygon := by
  intro j ε δ
  have hp := mul_le_mul_of_nonneg_left (hP j ε δ) (sub_nonneg.mpr hs1)
  have hq := mul_le_mul_of_nonneg_left (hQ j ε δ) hs0
  change (rowFirst j:ℝ)*((sign ε:ℝ)*((1-s)*P.1+s*Q.1))+
    (rowSecond j:ℝ)*((sign δ:ℝ)*((1-s)*P.2+s*Q.2))≤(rowConstant j:ℝ)
  nlinarith

/-- A whole closed REAL edge lies in the actual original polygon domain. -/
@[expose] def segmentPoint (v w : Fin 28) (s : ℝ) (hs0 : 0≤s) (hs1 : s≤1) : originalDomain :=
  polygonInverse ⟨realMix (realPoint (vertex v)) (realPoint (vertex w)) s,
    realMix_in_polygon _ _ (vertex_in_polygon v) (vertex_in_polygon w) s hs0 hs1⟩

theorem segment_coordinates (v w : Fin 28) (s : ℝ) (hs0 : 0≤s) (hs1 : s≤1) :
    (scaledFirst (segmentPoint v w s hs0 hs1).val,scaledSecond (segmentPoint v w s hs0 hs1).val)=
      realMix (realPoint (vertex v)) (realPoint (vertex w)) s :=
  Prod.ext (inverse_scaled _).1 (inverse_scaled _).2

theorem scaled_injective : Function.Injective (fun τ : HalfPlane => (scaledFirst τ,scaledSecond τ)) := by
  intro τ σ h
  apply toDisk_injective
  apply Subtype.ext
  apply Prod.ext
  · exact mul_left_cancel₀ (mul_ne_zero alpha_pos.ne' beta_pos.ne') (congrArg Prod.fst h)
  · exact mul_left_cancel₀ beta_pos.ne' (congrArg Prod.snd h)

/-- The actual original unit transports EVERY point of its closed real edge
to the exact corresponding point of the paired edge in the original upper half-plane. -/
theorem actual_unit_side (e : Fin 28) (s : ℝ) (hs0 : 0≤s) (hs1 : s≤1) :
    edgeUnit e • (segmentPoint (start e) (finish e) s hs0 hs1).val=
      (segmentPoint (imageStart e) (imageFinish e) s hs0 hs1).val := by
  apply scaled_injective
  have h := original_unit_equivariance (edgeUnit e)
    (segmentPoint (start e) (finish e) s hs0 hs1).val
  change _=realAction (realMatrix (embed (coefficients e)))
    (scaledFirst _,scaledSecond _) at h
  rw [segment_coordinates,actual_real_side] at h
  exact h.trans (segment_coordinates (imageStart e) (imageFinish e) s hs0 hs1).symm

theorem actual_side_height (e : Fin 28) (s : ℝ) (hs0 : 0≤s) (hs1 : s≤1) :
    height (segmentPoint (imageStart e) (imageFinish e) s hs0 hs1).val=
      height (segmentPoint (start e) (finish e) s hs0 hs1).val := by
  have h := original_height_multiplier (edgeUnit e)
    (segmentPoint (start e) (finish e) s hs0 hs1).val
  change _=denominator (realMatrix (embed (coefficients e)))
    (scaledFirst _,scaledSecond _)*_ at h
  rw [segment_coordinates,PELRealKleinSideTransport318.denominator_mix,
    denominator_cast,denominator_cast,(boundary_denominators e).1,(boundary_denominators e).2] at h
  norm_num only [Rat.cast_one,mul_one] at h
  rw [actual_unit_side] at h
  convert h using 1 <;> ring

/-- The central signs in the exact side-selection certificate disappear
ONLY in the quadratic real projective representation, not in the original order. -/
theorem selected_real_matrix (e : Fin 28) :
    realMatrix (embed (coefficients e))=
      realMatrix (embed (signedCoefficients (selection e).1 (selection e).2.1 (selection e).2.2)) := by
  have hs : centralSign e=1 ∨ centralSign e= -1 := by
    fin_cases e <;> norm_num [centralSign]
  rw [selected_coefficients]
  rcases hs with hs | hs
  · rw [hs,one_smul]
  · rw [hs,neg_one_smul,embed_neg]
    unfold realMatrix
    rw [PELQuaternionKleinAction318.matrix_neg]

theorem edge_test_action (e : Fin 28) (τ : HalfPlane) :
    edgeUnit e • τ=testUnit (selection e).1 (selection e).2.1 (selection e).2.2 • τ := by
  apply scaled_injective
  rw [original_unit_equivariance,original_unit_equivariance]
  change realAction (realMatrix (embed (coefficients e))) _=
    realAction (realMatrix (embed (signedCoefficients (selection e).1 (selection e).2.1 (selection e).2.2))) _
  rw [selected_real_matrix]

/-- Every whole-side pairing from the independent28-edge arithmetic table
is a GENERATOR of the already constructed actual polygon relation. -/
theorem actual_side_relation (e : Fin 28) (s : ℝ) (hs0 : 0≤s) (hs1 : s≤1) :
    sideRelation (segmentPoint (start e) (finish e) s hs0 hs1)
      (segmentPoint (imageStart e) (imageFinish e) s hs0 hs1) := by
  refine ⟨(selection e).1,(selection e).2.1,(selection e).2.2,?_,actual_side_height e s hs0 hs1⟩
  exact (actual_unit_side e s hs0 hs1).symm.trans (edge_test_action e _)

theorem original_paired_side (e : Fin 28) (s : ℝ) (hs0 : 0≤s) (hs1 : s≤1) :
    polygonProjection (segmentPoint (start e) (finish e) s hs0 hs1)=
      polygonProjection (segmentPoint (imageStart e) (imageFinish e) s hs0 hs1) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (actual_side_relation e s hs0 hs1))
end PELActualOriginalSideGluing318
