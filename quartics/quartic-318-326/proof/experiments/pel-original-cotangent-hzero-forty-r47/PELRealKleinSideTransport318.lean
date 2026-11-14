module
public import PELOriginalKleinEquivariance318
public import PELOriginalProjectiveTangents318
public section
noncomputable section
namespace PELRealKleinSideTransport318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 PELDirichletHeight318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELJointNormOneAction318
open PELQuaternionRealRepresentation318 PELDirichletSidePairingData318
open PELOriginalKleinEquivariance318 PELRealProjectiveDifferential318 PELOriginalProjectiveTangents318
set_option maxHeartbeats 1800000

@[expose] def realMix (P Q : ℝ×ℝ) (s : ℝ) : ℝ×ℝ :=
  ((1-s)*P.1+s*Q.1,(1-s)*P.2+s*Q.2)

/-- The same real three-row map used by the derivative producer is the
original Möbius action in the actual scaled Klein coordinates. -/
theorem original_unit_equivariance (u : normOneUnits) (τ : HalfPlane) :
    (scaledFirst (u • τ),scaledSecond (u • τ))=
      realAction (realMatrix ((u.val:order):B)) (scaledFirst τ,scaledSecond τ) := by
  let q : B := ((u.val:order):B)
  have hdet : (representation q).det=1 := by
    rw [PELPeriodDeterminant318.representation_det,(mem_normOneUnits u.val).mp u.property] <;> norm_num
  have h := original_scaled_action (representation q) hdet τ
  change (scaledFirst (matrixParameter (representation q) hdet τ),
    scaledSecond (matrixParameter (representation q) hdet τ))=_
  rw [realMatrix,PELQuaternionKleinAction318.original_real_matrix]
  exact Prod.ext h.1 h.2

theorem affine_mix (M : HomogeneousMatrix) (P Q : ℝ×ℝ) (s : ℝ) (i : Fin 3) :
    affineForm M i (realMix P Q s)=(1-s)*affineForm M i P+s*affineForm M i Q := by
  simp only [affineForm,realMix]
  ring

theorem denominator_mix (M : HomogeneousMatrix) (P Q : ℝ×ℝ) (s : ℝ) :
    denominator M (realMix P Q s)=(1-s)*denominator M P+s*denominator M Q := by
  simp only [←affineForm_value]
  exact affine_mix M P Q s 2

/-- Whole REAL side transport: no density or rational-point inference. -/
theorem real_action_mix (M : HomogeneousMatrix) (P Q : ℝ×ℝ) (s : ℝ)
    (hP : denominator M P=1) (hQ : denominator M Q=1) :
    realAction M (realMix P Q s)=realMix (realAction M P) (realAction M Q) s := by
  have hd : denominator M (realMix P Q s)=1 := by
    rw [denominator_mix,hP,hQ] <;> ring
  apply Prod.ext
  · simp only [realAction,realMix,hd,hP,hQ,div_one,←affineForm_value]
    exact affine_mix M P Q s 0
  · simp only [realAction,realMix,hd,hP,hQ,div_one,←affineForm_value]
    exact affine_mix M P Q s 1

theorem actual_real_side (e : Fin 28) (s : ℝ) :
    realAction (realMatrix (embed (coefficients e)))
      (realMix (realPoint (vertex (start e))) (realPoint (vertex (finish e))) s)=
      realMix (realPoint (vertex (imageStart e))) (realPoint (vertex (imageFinish e))) s := by
  have hP : denominator (realMatrix (embed (coefficients e))) (realPoint (vertex (start e)))=1 := by
    rw [denominator_cast,(boundary_denominators e).1] <;> norm_num
  have hQ : denominator (realMatrix (embed (coefficients e))) (realPoint (vertex (finish e)))=1 := by
    rw [denominator_cast,(boundary_denominators e).2] <;> norm_num
  rw [real_action_mix _ _ _ _ hP hQ,action_cast,action_cast,
    (endpoint_action e).1,(endpoint_action e).2]

/-- The real projective denominator is the ORIGINAL height multiplier. -/
theorem matrix_height_multiplier (M : RealMatrices) (hM : M.det=1) (τ : HalfPlane) :
    height (matrixParameter M hM τ)=originalVector M τ 2*height τ := by
  rw [(vector_values M τ).2.2]
  change (Complex.normSq (QuaternionicMobiusPeriods318.mobius M τ)+1)/
    (QuaternionicMobiusPeriods318.mobius M τ).im=_
  rw [PELDirichletHeight318.mobius_height M hM]
  have hn : Complex.normSq (τ:ℂ)+1≠0 := by nlinarith [Complex.normSq_nonneg (τ:ℂ)]
  unfold upperNorm lowerNorm height
  field_simp [hn,τ.property.ne'] <;> ring

theorem original_height_multiplier (u : normOneUnits) (τ : HalfPlane) :
    height (u • τ)=denominator (realMatrix ((u.val:order):B))
      (scaledFirst τ,scaledSecond τ)*height τ := by
  let q : B := ((u.val:order):B)
  have hdet : (representation q).det=1 := by
    rw [PELPeriodDeterminant318.representation_det,(mem_normOneUnits u.val).mp u.property] <;> norm_num
  rw [realMatrix,PELQuaternionKleinAction318.original_real_matrix]
  exact matrix_height_multiplier (representation q) hdet τ
end PELRealKleinSideTransport318
