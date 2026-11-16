module
public import PELDirichletVertexFan318
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public section
noncomputable section
namespace PELRealProjectiveDifferential318
open Matrix
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Point := ℝ × ℝ
abbrev HomogeneousMatrix := Matrix (Fin 3) (Fin 3) ℝ
@[expose] def affineForm (M : HomogeneousMatrix) (i : Fin 3) (P : Point) : ℝ :=
  M i 0*P.1+M i 1*P.2+M i 2
@[expose] def denominator (M : HomogeneousMatrix) (P : Point) : ℝ :=
  (M *ᵥ ![P.1,P.2,1]) 2
@[expose] def realAction (M : HomogeneousMatrix) (P : Point) : Point :=
  ((M *ᵥ ![P.1,P.2,1]) 0/denominator M P,
    (M *ᵥ ![P.1,P.2,1]) 1/denominator M P)

theorem affineForm_value (M : HomogeneousMatrix) (i : Fin 3) (P : Point) :
    affineForm M i P=(M *ᵥ ![P.1,P.2,1]) i := by
  simp [affineForm,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

@[expose] def linearRow (M : HomogeneousMatrix) (i : Fin 3) : Point →L[ℝ] ℝ :=
  M i 0 • ContinuousLinearMap.fst ℝ ℝ ℝ + M i 1 • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem affine_derivative (M : HomogeneousMatrix) (i : Fin 3) (P : Point) :
    HasFDerivAt (affineForm M i) (linearRow M i) P := by
  exact (((hasFDerivAt_fst (𝕜 := ℝ) (p := P)).const_mul (M i 0)).add
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := P)).const_mul (M i 1)) |>.add_const (M i 2)

/-- Product-rule form of the literal quotient derivative, before scalar simplification. -/
@[expose] def quotientRow (M : HomogeneousMatrix) (P : Point) (i : Fin 3) : Point →L[ℝ] ℝ :=
  affineForm M i P • (-(affineForm M 2 P ^ 2)⁻¹ • linearRow M 2) +
    (affineForm M 2 P)⁻¹ • linearRow M i
@[expose] def differential (M : HomogeneousMatrix) (P : Point) : Point →L[ℝ] Point :=
  (quotientRow M P 0).prod (quotientRow M P 1)

theorem quotient_derivative (M : HomogeneousMatrix) (P : Point)
    (hP : affineForm M 2 P≠0) (i : Fin 3) :
    HasFDerivAt (fun Q => affineForm M i Q/affineForm M 2 Q) (quotientRow M P i) P := by
  have hinv := (hasDerivAt_inv hP).comp_hasFDerivAt P (affine_derivative M 2 P)
  simpa only [quotientRow,div_eq_mul_inv,Function.comp_apply] using
    (affine_derivative M i P).mul hinv

/-- Actual real Frechet derivative of the SAME three-row projective action. -/
theorem hasFDerivAt_realAction (M : HomogeneousMatrix) (P : Point)
    (hP : denominator M P≠0) : HasFDerivAt (realAction M) (differential M P) P := by
  have hd : affineForm M 2 P≠0 := by rwa [affineForm_value]
  simpa only [realAction,denominator,differential,affineForm_value] using
    (quotient_derivative M P hd 0).prodMk (quotient_derivative M P hd 1)

theorem quotientRow_apply (M : HomogeneousMatrix) (P W : Point)
    (hP : denominator M P≠0) (i : Fin 3) :
    quotientRow M P i W=
      ((M i 0*W.1+M i 1*W.2)*denominator M P-
        affineForm M i P*(M 2 0*W.1+M 2 1*W.2))/(denominator M P)^2 := by
  have hd : affineForm M 2 P≠0 := by rwa [affineForm_value]
  change affineForm M i P * (-(affineForm M 2 P ^ 2)⁻¹ *
      (M 2 0*W.1+M 2 1*W.2)) +
    (affineForm M 2 P)⁻¹*(M i 0*W.1+M i 1*W.2) = _
  have he : denominator M P=affineForm M 2 P := (affineForm_value M 2 P).symm
  rw [he]
  field_simp [hd] <;> ring

@[expose] def jacobian (M : HomogeneousMatrix) (P : Point) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(M 0 0*denominator M P-affineForm M 0 P*M 2 0)/(denominator M P)^2,
      (M 0 1*denominator M P-affineForm M 0 P*M 2 1)/(denominator M P)^2;
     (M 1 0*denominator M P-affineForm M 1 P*M 2 0)/(denominator M P)^2,
      (M 1 1*denominator M P-affineForm M 1 P*M 2 1)/(denominator M P)^2]

/-- The exact denominator cube in the projective Jacobian is retained. -/
theorem jacobian_det (M : HomogeneousMatrix) (P : Point) (hP : denominator M P≠0) :
    (jacobian M P).det=M.det/(denominator M P)^3 := by
  rw [jacobian,Matrix.det_fin_two,Matrix.det_fin_three]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  field_simp [hP]
  simp only [denominator,affineForm,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,mul_one]
  ring

theorem jacobian_positive (M : HomogeneousMatrix) (P : Point)
    (hM : 0<M.det) (hP : 0<denominator M P) : 0<(jacobian M P).det := by
  rw [jacobian_det M P hP.ne']
  exact div_pos hM (pow_pos hP 3)
theorem differential_apply (M : HomogeneousMatrix) (P W : Point)
    (hP : denominator M P≠0) :
    differential M P W=
      (jacobian M P 0 0*W.1+jacobian M P 0 1*W.2,
       jacobian M P 1 0*W.1+jacobian M P 1 1*W.2) := by
  apply Prod.ext
  · change quotientRow M P 0 W=_
    rw [quotientRow_apply M P W hP]
    simp only [jacobian,Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  · change quotientRow M P 1 W=_
    rw [quotientRow_apply M P W hP]
    simp only [jacobian,Matrix.cons_val_zero,Matrix.cons_val_one]
    ring

@[expose] def inverseTangent (M : HomogeneousMatrix) (P W : Point) : Point :=
  ((jacobian M P 1 1*W.1-jacobian M P 0 1*W.2)/(jacobian M P).det,
   (-jacobian M P 1 0*W.1+jacobian M P 0 0*W.2)/(jacobian M P).det)

theorem inverse_differential (M : HomogeneousMatrix) (P W : Point)
    (hP : denominator M P≠0) (hJ : (jacobian M P).det≠0) :
    inverseTangent M P (differential M P W)=W := by
  rw [differential_apply M P W hP]
  apply Prod.ext <;> simp only [inverseTangent,Prod.fst,Prod.snd]
  all_goals field_simp [hJ]
  all_goals rw [Matrix.det_fin_two]
  all_goals ring

theorem differential_inverse (M : HomogeneousMatrix) (P W : Point)
    (hP : denominator M P≠0) (hJ : (jacobian M P).det≠0) :
    differential M P (inverseTangent M P W)=W := by
  rw [differential_apply M P _ hP]
  apply Prod.ext <;> simp only [inverseTangent,Prod.fst,Prod.snd]
  all_goals field_simp [hJ]
  all_goals rw [Matrix.det_fin_two]
  all_goals ring

/-- Actual derivative invertibility, with an explicit inverse on the SAME
real tangent coordinates, rather than only a nonzero determinant claim. -/
theorem differential_bijective (M : HomogeneousMatrix) (P : Point)
    (hP : denominator M P≠0) (hM : M.det≠0) : Function.Bijective (differential M P) := by
  have hJ : (jacobian M P).det≠0 := by
    rw [jacobian_det M P hP]
    exact div_ne_zero hM (pow_ne_zero 3 hP)
  constructor
  · intro V W h
    have hh := congrArg (inverseTangent M P) h
    simpa only [inverse_differential M P _ hP hJ] using hh
  · intro W
    exact ⟨inverseTangent M P W,differential_inverse M P W hP hJ⟩
end PELRealProjectiveDifferential318
