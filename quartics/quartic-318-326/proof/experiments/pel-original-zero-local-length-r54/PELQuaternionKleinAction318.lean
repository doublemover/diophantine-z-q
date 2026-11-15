module
public import PELOriginalLocalAlgebraClassification318
public section
noncomputable section
namespace PELQuaternionKleinAction318
open PELQuaternionAlgebra318 QuaternionAlgebra Matrix
set_option maxHeartbeats 1800000
abbrev Point := ℚ × ℚ
abbrev Vector := Fin 3 → ℚ

/-- Exact homogeneous Klein coordinates (A,B,T) for the ORIGINAL real
matrix action, scaled by sqrt1050 and sqrt5. The normalization divides all
three rows by2, so the identity quaternion maps to the identity matrix. -/
@[expose] def matrix (q : B) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![q.re^2-5*q.imJ^2-210*q.imI^2+1050*q.imK^2,
       420*(q.re*q.imI+5*q.imJ*q.imK),2100*(q.re*q.imK+q.imI*q.imJ);
     -2*(q.re*q.imI-5*q.imJ*q.imK),
       q.re^2+5*q.imJ^2-210*q.imI^2-1050*q.imK^2,10*(q.re*q.imJ-210*q.imI*q.imK);
     2*(q.re*q.imK-q.imI*q.imJ),2*q.re*q.imJ+420*q.imI*q.imK,
       q.re^2+210*q.imI^2+5*q.imJ^2+1050*q.imK^2]

theorem matrix_one : matrix (1:B)=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [matrix]

theorem matrix_mul (q r : B) : matrix (q*r)=matrix q*matrix r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,Matrix.mul_apply,Fin.sum_univ_three] <;> ring

theorem matrix_neg (q : B) : matrix (-q)=matrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix] <;> ring

@[expose] def homogeneous : B →* Matrix (Fin 3) (Fin 3) ℚ where
  toFun := matrix
  map_one' := matrix_one
  map_mul' := matrix_mul

open PELQuaternionRealRepresentation318 (alpha beta alpha_pos beta_pos alpha_sq beta_sq)

/-- The scaled symmetric-square matrix of the ACTUAL real2x2 action.
Its columns are A,B,T, with A=sqrt1050*u and B=sqrt5*v. -/
@[expose] def realHomogeneous (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![M 0 0*M 1 1+M 0 1*M 1 0,
      alpha*(M 0 0*M 1 0-M 0 1*M 1 1),
      alpha*beta*(M 0 0*M 1 0+M 0 1*M 1 1);
    (M 0 0*M 0 1-M 1 0*M 1 1)/alpha,
      (M 0 0^2-M 0 1^2-M 1 0^2+M 1 1^2)/2,
      beta*(M 0 0^2+M 0 1^2-M 1 0^2-M 1 1^2)/2;
    (M 0 0*M 0 1+M 1 0*M 1 1)/(alpha*beta),
      (M 0 0^2+M 1 0^2-M 0 1^2-M 1 1^2)/(2*beta),
      (M 0 0^2+M 0 1^2+M 1 0^2+M 1 1^2)/2]

theorem original_real_matrix (q : B) :
    (matrix q).map (algebraMap ℚ ℝ)=
      realHomogeneous (PELQuaternionRealRepresentation318.representation q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,realHomogeneous,PELQuaternionRealRepresentation318.representation,
      PELQuaternionRealRepresentation318.matrix] <;>
    push_cast <;> field_simp [alpha_pos.ne',beta_pos.ne'] <;>
    ring_nf <;> simp only [alpha_sq,beta_sq] <;> ring

@[expose] def quadratic (v : Vector) : ℚ := v 2^2-v 0^2/1050-v 1^2/5

/-- The original reduced norm controls the SAME homogeneous quadratic
form; there is no substituted elliptic or j-map representation. -/
theorem quadratic_action (q : B) (v : Vector) :
    quadratic (matrix q *ᵥ v)=(reducedNorm q)^2*quadratic v := by
  simp [quadratic,matrix,reducedNorm,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  ring

@[expose] def vector (P : Point) : Vector := ![P.1,P.2,1]
@[expose] def denominator (q : B) (P : Point) : ℚ := (matrix q *ᵥ vector P) 2
@[expose] def action (q : B) (P : Point) : Point :=
  ((matrix q *ᵥ vector P) 0/denominator q P,
    (matrix q *ᵥ vector P) 1/denominator q P)

theorem denominator_value (q : B) (P : Point) :
    denominator q P=2*(q.re*q.imK-q.imI*q.imJ)*P.1+
      (2*q.re*q.imJ+420*q.imI*q.imK)*P.2+
      q.re^2+210*q.imI^2+5*q.imJ^2+1050*q.imK^2 := by
  simp [denominator,matrix,vector,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  ring

theorem action_neg (q : B) (P : Point) : action (-q) P=action q P := by
  simp only [action,denominator,matrix_neg]

/-- Every point of the actual scaled disk has a valid affine image under
every nonzero original quaternion, derived from the original norm identity. -/
theorem denominator_ne (q : B) (hq : q≠0) (P : Point)
    (hP : P.1^2/1050+P.2^2/5<1) : denominator q P≠0 := by
  have hn := PELQuaternionAnisotropy318.reducedNorm_ne_zero q hq
  have hpos : 0<(reducedNorm q)^2*quadratic (vector P) := by
    apply mul_pos (sq_pos_of_ne_zero hn)
    simp only [quadratic,vector,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,one_pow]
    linarith
  have h := quadratic_action q (vector P)
  intro hd
  change (matrix q *ᵥ vector P) 2=0 at hd
  rw [quadratic,hd,zero_pow (by decide)] at h
  have h0 := sq_nonneg ((matrix q *ᵥ vector P) 0)
  have h1 := sq_nonneg ((matrix q *ᵥ vector P) 1)
  nlinarith

theorem action_disk (q : B) (hq : q≠0) (P : Point)
    (hP : P.1^2/1050+P.2^2/5<1) :
    (action q P).1^2/1050+(action q P).2^2/5<1 := by
  have hd := denominator_ne q hq P hP
  have hn := PELQuaternionAnisotropy318.reducedNorm_ne_zero q hq
  have h := quadratic_action q (vector P)
  have hpos : 0<(reducedNorm q)^2*quadratic (vector P) := by
    apply mul_pos (sq_pos_of_ne_zero hn)
    simp only [quadratic,vector,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,one_pow]
    linarith
  change ((matrix q *ᵥ vector P) 0/denominator q P)^2/1050+
    ((matrix q *ᵥ vector P) 1/denominator q P)^2/5<1
  have hdpos : 0<(denominator q P)^2 := sq_pos_of_ne_zero hd
  have hquad : 0<(denominator q P)^2-
      (matrix q *ᵥ vector P) 0^2/1050-(matrix q *ᵥ vector P) 1^2/5 := by
    change 0<quadratic (matrix q *ᵥ vector P)
    rw [h]
    exact hpos
  apply (mul_lt_mul_right hdpos).mp
  have heq : (((matrix q *ᵥ vector P) 0/denominator q P)^2/1050+
      ((matrix q *ᵥ vector P) 1/denominator q P)^2/5)*(denominator q P)^2=
      (matrix q *ᵥ vector P) 0^2/1050+(matrix q *ᵥ vector P) 1^2/5 := by
    field_simp [hd] <;> ring
  rw [heq]
  nlinarith
/-- Affine interpolation in the actual scaled Klein coordinates. -/
@[expose] def mix (P Q : Point) (s : ℚ) : Point :=
  ((1-s)*P.1+s*Q.1,(1-s)*P.2+s*Q.2)

theorem homogeneous_mix (q : B) (P Q : Point) (s : ℚ) (i : Fin 3) :
    (matrix q *ᵥ vector (mix P Q s)) i =
      (1-s)*(matrix q *ᵥ vector P) i+s*(matrix q *ᵥ vector Q) i := by
  simp [mix,vector,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  ring

theorem denominator_mix (q : B) (P Q : Point) (s : ℚ) :
    denominator q (mix P Q s)=(1-s)*denominator q P+s*denominator q Q :=
  homogeneous_mix q P Q s 2

/-- On a unit-energy side the original projective map is literally affine.
This identifies the whole side, rather than only its two listed endpoints. -/
theorem action_mix (q : B) (P Q : Point) (s : ℚ)
    (hP : denominator q P=1) (hQ : denominator q Q=1) :
    action q (mix P Q s)=mix (action q P) (action q Q) s := by
  have hd : denominator q (mix P Q s)=1 := by
    rw [denominator_mix,hP,hQ]
    ring
  apply Prod.ext
  · change (matrix q *ᵥ vector (mix P Q s)) 0/denominator q (mix P Q s)=
      (1-s)*((matrix q *ᵥ vector P) 0/denominator q P)+
        s*((matrix q *ᵥ vector Q) 0/denominator q Q)
    rw [homogeneous_mix,hd,hP,hQ] <;> simp only [div_one]
  · change (matrix q *ᵥ vector (mix P Q s)) 1/denominator q (mix P Q s)=
      (1-s)*((matrix q *ᵥ vector P) 1/denominator q P)+
        s*((matrix q *ᵥ vector Q) 1/denominator q Q)
    rw [homogeneous_mix,hd,hP,hQ] <;> simp only [div_one]
end PELQuaternionKleinAction318
