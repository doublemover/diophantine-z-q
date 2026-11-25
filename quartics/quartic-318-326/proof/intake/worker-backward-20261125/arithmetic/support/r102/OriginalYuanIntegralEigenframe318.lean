module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
Exact construction of the two ordered integral Lie eigenvectors in the
original smooth component. Starting from its actual spectral projector
P, choose an invertible two-column frame locally. No division by 2, no
residue-field or generic-basis approximation, and no new coefficient field.
-/
@[expose] public section

namespace OriginalYuanIntegralEigenframe318

abbrev Mat (R : Type*) := Matrix (Fin 2) (Fin 2) R

variable {R : Type*} [CommRing R]

abbrev eFirst : Mat R := !![1, 0; 0, 0]

/-- Ordered eigenvector columns: P applied to the first vector and
1−P to the second vector. -/
def leftPivot (P : Mat R) : Mat R :=
  !![P 0 0, -(P 0 1); P 1 0, 1-P 1 1]

/-- The second pivot when the other diagonal entry of P is a unit. -/
def rightPivot (P : Mat R) : Mat R :=
  !![P 0 1, 1-P 0 0; P 1 1, -(P 1 0)]

private theorem on_entries (P : Mat R) (h : P*P=P) (i j : Fin 2) :
    P i 0 * P 0 j + P i 1 * P 1 j = P i j := by
  have q := congrArg (fun Q : Mat R => Q i j) h
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using q

theorem left_read (P : Mat R) (h : P * P = P) :
    P * leftPivot P = leftPivot P * eFirst := by
  have h00 := on_entries P h 0 0
  have h01 := on_entries P h 0 1
  have h10 := on_entries P h 1 0
  have h11 := on_entries P h 1 1
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [leftPivot, Matrix.mul_apply, Fin.sum_univ_two] using h00
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    change P 0 0 * (-(P 0 1)) + P 0 1 * (1-P 1 1) =
      P 0 0 * 0 + (-(P 0 1)) * 0
    linear_combination -h01
  · simpa [leftPivot, Matrix.mul_apply, Fin.sum_univ_two] using h10
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    change P 1 0 * (-(P 0 1)) + P 1 1 * (1-P 1 1) =
      P 1 0 * 0 + (1-P 1 1) * 0
    linear_combination -h11

theorem right_read (P : Mat R) (h : P * P = P) :
    P * rightPivot P = rightPivot P * eFirst := by
  have h00 := on_entries P h 0 0
  have h01 := on_entries P h 0 1
  have h10 := on_entries P h 1 0
  have h11 := on_entries P h 1 1
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [rightPivot, Matrix.mul_apply, Fin.sum_univ_two] using h01
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    change P 0 0 * (1-P 0 0) + P 0 1 * (-(P 1 0)) =
      P 0 1 * 0 + (1-P 0 0) * 0
    linear_combination -h00
  · simpa [rightPivot, Matrix.mul_apply, Fin.sum_univ_two] using h11
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    change P 1 0 * (1-P 0 0) + P 1 1 * (-(P 1 0)) =
      P 1 1 * 0 + (-(P 1 0)) * 0
    linear_combination -h10

theorem left_det (P : Mat R) (h : P*P=P) (tr : P 0 0 + P 1 1 = 1) :
    Matrix.det (leftPivot P) = P 0 0 := by
  rw [Matrix.det_fin_two]
  change P 0 0 * (1-P 1 1) - (-(P 0 1))*P 1 0 = P 0 0
  have hp := on_entries P h 0 0
  linear_combination hp - (P 0 0)*tr

theorem right_det (P : Mat R) (h : P*P=P) (tr : P 0 0 + P 1 1 = 1) :
    Matrix.det (rightPivot P) = -(P 1 1) := by
  rw [Matrix.det_fin_two]
  change P 0 1 * (-(P 1 0)) - (1-P 0 0)*P 1 1 = -(P 1 1)
  have hp := on_entries P h 1 1
  linear_combination -hp + (P 1 1)*tr

/-- The actual primitive ordered frame is constructed without choosing
two independently lifted eigenlines. The determinant is a unit on this
very structural local ring. -/
theorem frame [IsLocalRing R] (P : Mat R) (h : P*P=P)
    (tr : P 0 0 + P 1 1 = 1) :
    ∃ S : Mat R, IsUnit (Matrix.det S) ∧ P*S=S*eFirst := by
  have H : IsUnit (P 0 0 + P 1 1) := tr.symm ▸ isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add H with hl | hr
  · exact ⟨leftPivot P, (left_det P h tr).symm ▸ hl, left_read P h⟩
  · exact ⟨rightPivot P, (right_det P h tr).symm ▸ hr.neg, right_read P h⟩

/-- The trace condition follows from the original two reduced norm
reads, det(f)=-1 and det(1+f)=1; no residue characteristic exception. -/
theorem trace_from_order_norms (F : Mat R)
    (detF : Matrix.det F = -1) (detFone : Matrix.det (F+1)=1) :
    F 0 0 + F 1 1 = 1 := by
  rw [Matrix.det_fin_two] at detF detFone
  simp [Matrix.one_apply] at detFone
  linear_combination detFone - detF

def projector (F : Mat R) (v : R) (U : Rˣ) : Mat R :=
  (↑U⁻¹ : R) • (F - v • (1 : Mat R))

theorem proj_eigen (F : Mat R) (u v : R) (U : Rˣ)
    (sumroots : u+v=1) (prodroots : u*v= -1) (poly : F*F=F+1) :
    F*projector F v U = u • projector F v U := by
  have h : F*(F-v • (1:Mat R)) = u • (F-v • (1:Mat R)) := by
    rw [mul_sub,mul_smul_comm,mul_one,poly]
    ext i j
    change F i j+(1:Mat R) i j-v*F i j = u*(F i j-v*(1:Mat R) i j)
    linear_combination -(F i j)*sumroots + ((1:Mat R) i j)*prodroots
  rw [projector,mul_smul_comm,h,smul_smul,smul_smul,mul_comm (↑U⁻¹ : R) u]

theorem proj_idem (F : Mat R) (u v : R) (U : Rˣ) (hv : (↑U : R)=u-v)
    (sumroots : u+v=1) (prodroots : u*v= -1) (poly : F*F=F+1) :
    projector F v U * projector F v U = projector F v U := by
  let P := projector F v U
  have hm : F*P=u•P := proj_eigen F u v U sumroots prodroots poly
  change ((↑U⁻¹:R) • (F - v • (1:Mat R))) * P = P
  rw [smul_mul_assoc,sub_mul,hm,smul_mul_assoc,one_mul,←sub_smul,smul_smul,←hv]
  simp

theorem proj_trace (F : Mat R) (u v : R) (U : Rˣ) (hv : (↑U : R)=u-v)
    (sumroots : u+v=1) (traceF : F 0 0+F 1 1=1) :
    projector F v U 0 0 + projector F v U 1 1 = 1 := by
  have hu : (↑U⁻¹:R)*(u-v)=1 := by rw [←hv]; simp
  change (↑U⁻¹:R)*(F 0 0-v*(1:Mat R) 0 0) +
      (↑U⁻¹:R)*(F 1 1-v*(1:Mat R) 1 1)=1
  simp [Matrix.one_apply]
  linear_combination (↑U⁻¹:R)*traceF - (↑U⁻¹:R)*sumroots + hu

/-- Produce the genuine oriented f-eigenframe from the actual original
operator and its determinant reads. No extra frame assumption is used. -/
theorem from_actual_f [IsLocalRing R] (F : Mat R) (u v : R)
    (gap : IsUnit (u-v)) (sumroots : u+v=1) (prodroots : u*v= -1)
    (poly : F*F=F+1) (detF : Matrix.det F = -1) (detFone : Matrix.det (F+1)=1) :
    ∃ S : Mat R, IsUnit (Matrix.det S) ∧ F*S=S* (!![u,0;0,v] : Mat R) := by
  obtain ⟨U,hU⟩ := gap
  let P := projector F v U
  obtain ⟨S,sdet,sP⟩ := frame P
    (proj_idem F u v U hU sumroots prodroots poly)
    (proj_trace F u v U hU sumroots (trace_from_order_norms F detF detFone))
  have hF : v • (1:Mat R) + (u-v)•P = F := by
    change v • (1:Mat R) + (u-v)•((↑U⁻¹:R) • (F-v • (1:Mat R))) = F
    rw [smul_smul, ← hU]
    simp
  have hD : v • (1:Mat R) + (u-v) • eFirst = (!![u,0;0,v] : Mat R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> ring
  refine ⟨S,sdet,?_⟩
  calc
    F*S = (v • (1:Mat R) + (u-v)•P)*S := congrArg (fun M => M*S) hF.symm
    _ = v•S + (u-v)•(S*eFirst) := by
      rw [add_mul,smul_mul_assoc,one_mul,smul_mul_assoc,sP]
    _ = S*(v • (1:Mat R) + (u-v)•eFirst) := by
      rw [mul_add,mul_smul_comm,mul_one,mul_smul_comm]
    _ = _ := by rw [hD]

/-- In that very f-frame the actual left g switches summands, and its
square 42 certifies the product of its literal off-diagonal entries. -/
theorem actual_switch (u v : R) (gap : IsUnit (u-v)) (G : Mat R)
    (switches : G*(!![u,0;0,v] : Mat R) = (!![v,0;0,u] : Mat R)*G)
    (sq : G*G=(42:R) • (1:Mat R)) :
    G=(!![0,G 0 1;G 1 0,0] : Mat R) ∧ G 1 0 * G 0 1 = 42 := by
  have h₀ := congrArg (fun M : Mat R => M 0 0) switches
  have h₁ := congrArg (fun M : Mat R => M 1 1) switches
  simp [Matrix.mul_apply,Fin.sum_univ_two] at h₀ h₁
  have z₀ : G 0 0 = 0 := by
    apply gap.mul_right_cancel
    linear_combination h₀
  have z₁ : G 1 1 = 0 := by
    apply gap.mul_right_cancel
    linear_combination -h₁
  refine ⟨?_,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [z₀,z₁]
  · have e := congrArg (fun M : Mat R => M 1 1) sq
    simpa [Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,z₁] using e

end OriginalYuanIntegralEigenframe318

#print axioms OriginalYuanIntegralEigenframe318.left_read
#print axioms OriginalYuanIntegralEigenframe318.right_read
#print axioms OriginalYuanIntegralEigenframe318.frame
#print axioms OriginalYuanIntegralEigenframe318.from_actual_f
#print axioms OriginalYuanIntegralEigenframe318.actual_switch
