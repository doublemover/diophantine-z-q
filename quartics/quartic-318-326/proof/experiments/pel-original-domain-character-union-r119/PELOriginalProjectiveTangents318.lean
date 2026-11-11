module
public import PELRealProjectiveDifferential318
public section
noncomputable section
namespace PELOriginalProjectiveTangents318
open PELQuaternionAlgebra318
open PELQuaternionKleinAction318 PELDirichletVertexFan318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] def realPoint (P : PELQuaternionKleinAction318.Point) : ℝ × ℝ :=
  ((P.1:ℝ),(P.2:ℝ))
@[expose] def realMatrix (q : B) : Matrix (Fin 3) (Fin 3) ℝ :=
  (matrix q).map (algebraMap ℚ ℝ)

/-- This is the symmetric-square matrix of the original faithful real
representation, not a second action on an unrelated disk. -/
theorem original_real_action_matrix (q : B) :
    realMatrix q=realHomogeneous (PELQuaternionRealRepresentation318.representation q) :=
  original_real_matrix q

theorem denominator_cast (q : B) (P : PELQuaternionKleinAction318.Point) :
    PELRealProjectiveDifferential318.denominator (realMatrix q) (realPoint P)=
      (denominator q P:ℝ) := by
  simp [PELRealProjectiveDifferential318.denominator,realMatrix,realPoint,
    denominator,vector,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem action_cast (q : B) (P : PELQuaternionKleinAction318.Point) :
    PELRealProjectiveDifferential318.realAction (realMatrix q) (realPoint P)=
      realPoint (action q P) := by
  apply Prod.ext <;>
    simp [PELRealProjectiveDifferential318.realAction,denominator_cast,realMatrix,
      realPoint,action,vector,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem homogeneous_det (q : B) : (matrix q).det=(reducedNorm q)^3 := by
  rw [Matrix.det_fin_three]
  simp only [matrix,reducedNorm,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  ring

theorem realMatrix_det (q : B) : (realMatrix q).det=(reducedNorm q:ℝ)^3 := by
  have h := congrArg (fun x : ℚ => (x:ℝ)) (homogeneous_det q)
  simpa only [Rat.cast_det,realMatrix,Rat.cast_pow] using h

/-- Actual derivative evaluated on a rational original tangent is the
scalar extension of the EXACT rational quotient-rule expression already
used in the side-cycle certificate. -/
theorem differential_cast (q : B) (P W : PELQuaternionKleinAction318.Point)
    (hP : denominator q P≠0) :
    PELRealProjectiveDifferential318.differential (realMatrix q) (realPoint P) (realPoint W)=
      realPoint (tangentFormula q P W) := by
  have hd : PELRealProjectiveDifferential318.denominator (realMatrix q) (realPoint P)≠0 := by
    rw [denominator_cast]
    exact_mod_cast hP
  apply Prod.ext
  · change PELRealProjectiveDifferential318.quotientRow (realMatrix q) (realPoint P) 0
      (realPoint W)=_
    rw [PELRealProjectiveDifferential318.quotientRow_apply _ _ _ hd]
    simp [tangentFormula,realMatrix,realPoint,denominator_cast,
      PELRealProjectiveDifferential318.affineForm,denominator,vector,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  · change PELRealProjectiveDifferential318.quotientRow (realMatrix q) (realPoint P) 1
      (realPoint W)=_
    rw [PELRealProjectiveDifferential318.quotientRow_apply _ _ _ hd]
    simp [tangentFormula,realMatrix,realPoint,denominator_cast,
      PELRealProjectiveDifferential318.affineForm,denominator,vector,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem actual_differential_bijective (q : B) (hq : q≠0) (P : ℝ × ℝ)
    (hP : PELRealProjectiveDifferential318.denominator (realMatrix q) P≠0) :
    Function.Bijective (PELRealProjectiveDifferential318.differential (realMatrix q) P) := by
  apply PELRealProjectiveDifferential318.differential_bijective _ _ hP
  rw [realMatrix_det]
  apply pow_ne_zero
  exact_mod_cast PELQuaternionAnisotropy318.reducedNorm_ne_zero q hq

/-- Positive original norm and positive projective denominator give the
actual orientation sign, including the exact denominator cube. -/
theorem actual_orientation (q : B) (hq : 0<reducedNorm q) (P : ℝ × ℝ)
    (hP : 0<PELRealProjectiveDifferential318.denominator (realMatrix q) P) :
    0<(PELRealProjectiveDifferential318.jacobian (realMatrix q) P).det := by
  apply PELRealProjectiveDifferential318.jacobian_positive _ _ _ hP
  rw [realMatrix_det]
  apply pow_pos
  exact_mod_cast hq
end PELOriginalProjectiveTangents318
