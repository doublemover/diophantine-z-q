module
public import OriginalSameJRealificationDet318
public import Mathlib.Algebra.Ring.Parity

@[expose] public section
noncomputable section

namespace OriginalSameJSymplecticPeriods318

open Matrix OriginalSameJRealificationDet318
open scoped ComplexConjugate Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

def groupedReal (P Q : Mat ℂ I) : Mat ℝ (I ⊕ I) :=
  fromBlocks (P.map Complex.re) (Q.map Complex.re) (P.map Complex.im) (Q.map Complex.im)

def complexPeriods (P Q : Mat ℂ I) : Mat ℂ (I ⊕ I) :=
  fromBlocks P Q (P.map (starRingEnd ℂ)) (Q.map (starRingEnd ℂ))

def standardJ : Mat ℂ (I ⊕ I) := fromBlocks 0 1 (-1) 0

def complexIsotropy (P Q : Mat ℂ I) : Mat ℂ I := P * Qᵀ - Q * Pᵀ
def mixedPairing (P Q : Mat ℂ I) : Mat ℂ I :=
  (P.map (starRingEnd ℂ)) * Qᵀ - (Q.map (starRingEnd ℂ)) * Pᵀ

theorem whole_complexification (P Q : Mat ℂ I) :
    rotations (I:=I) * (groupedReal P Q).map Complex.ofReal = complexPeriods P Q := by
  unfold rotations groupedReal complexPeriods
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  simp only [Matrix.one_mul,Matrix.smul_mul]
  refine ⟨?_,?_,?_,?_⟩ <;> ext i j <;> apply Complex.ext <;>
    simp [Matrix.add_apply,Matrix.smul_apply,Matrix.map_apply,Complex.mul_re,Complex.mul_im]

private theorem j_sq : standardJ (I:=I) * standardJ = -(1 : Mat ℂ (I ⊕ I)) := by
  unfold standardJ
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks]

private theorem j_det_sq : (standardJ (I:=I)).det ^ 2 = 1 := by
  have hj := congrArg Matrix.det (j_sq (I:=I))
  rw [Matrix.det_mul,Matrix.det_neg,Matrix.det_one,mul_one,Fintype.card_sum] at hj
  have he : Even (Fintype.card I + Fintype.card I) := ⟨Fintype.card I,rfl⟩
  rw [he.neg_one_pow] at hj
  simpa only [pow_two] using hj

private theorem conjugate_isotropic (P Q : Mat ℂ I) (h : complexIsotropy P Q=0) :
    (P.map (starRingEnd ℂ)) * (Q.map (starRingEnd ℂ))ᵀ -
       (Q.map (starRingEnd ℂ)) * (P.map (starRingEnd ℂ))ᵀ = 0 := by
  have h' : P * Qᵀ = Q * Pᵀ := sub_eq_zero.mp h
  have hx := congrArg ((starRingEnd ℂ).mapMatrix) h'
  rw [map_mul,map_mul] at hx
  exact sub_eq_zero.mpr hx

omit [DecidableEq I] in
private theorem mixed_transpose (P Q : Mat ℂ I) :
    P * (Q.map (starRingEnd ℂ))ᵀ - Q * (P.map (starRingEnd ℂ))ᵀ =
      -(mixedPairing P Q)ᵀ := by
  rw [mixedPairing,Matrix.transpose_sub,Matrix.transpose_mul,Matrix.transpose_mul,
    Matrix.transpose_transpose,Matrix.transpose_transpose,neg_sub]

/-- For actual symplectic periods, use the FIRST bilinear relation in its
literal isotropy form and the SECOND with conjugation on the first slot. -/
theorem bilinear_blocks (P Q : Mat ℂ I)
    (h : complexIsotropy P Q=0) :
    complexPeriods P Q * standardJ * (complexPeriods P Q)ᵀ * standardJ =
      fromBlocks (mixedPairing P Q)ᵀ 0 0 (mixedPairing P Q) := by
  have hC := conjugate_isotropic P Q h
  unfold complexPeriods standardJ
  simp only [Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,Matrix.mul_one,
    Matrix.mul_zero,Matrix.neg_mul,Matrix.mul_neg,
    add_zero,zero_add]
  have h' : -(Q * Pᵀ) + P * Qᵀ=0 := by simpa only [complexIsotropy,sub_eq_add_neg,add_comm] using h
  have hc' :
      -((Q.map (starRingEnd ℂ)) * (P.map (starRingEnd ℂ))ᵀ) +
        (P.map (starRingEnd ℂ)) * (Q.map (starRingEnd ℂ))ᵀ=0 := by
    simpa only [sub_eq_add_neg,add_comm] using hC
  have hm :
      -(Q * (P.map (starRingEnd ℂ))ᵀ) + P * (Q.map (starRingEnd ℂ))ᵀ =
        -(mixedPairing P Q)ᵀ := by
    simpa only [sub_eq_add_neg,add_comm] using mixed_transpose P Q
  have hm' :
      -((Q.map (starRingEnd ℂ)) * Pᵀ) + (P.map (starRingEnd ℂ)) * Qᵀ =
        mixedPairing P Q := by
    simp only [mixedPairing,sub_eq_add_neg,add_comm]
  rw [h',hc',hm,hm']
  simp only [neg_neg,neg_zero]

private theorem complex_det (P Q : Mat ℂ I) :
    (complexPeriods P Q).det =
      ((-Complex.I)-Complex.I)^Fintype.card I * ((groupedReal P Q).det : ℂ) := by
  have hh := congrArg Matrix.det (whole_complexification P Q)
  rw [Matrix.det_mul,rotations_det_value] at hh
  have hmap : ((groupedReal P Q).map Complex.ofReal).det = ((groupedReal P Q).det : ℂ) :=
    (Complex.ofRealHom.map_det _).symm
  rw [hmap] at hh
  exact hh.symm

/-- Exact period determinant, with no normalized A-block, no choice of
symplectic coordinates beyond the actual cycle basis, and no determinant
factor taken as a premise. The scalar read is 2i times the true Gram. -/
theorem actual_determinant (P Q G : Mat ℂ I)
    (h : complexIsotropy P Q=0)
    (hG : mixedPairing P Q = ((2:ℂ)*Complex.I) • G) (hpos : 0 < G.det.re) :
    |(groupedReal P Q).det| = G.det.re := by
  let a : ℂ := 2*Complex.I
  have ha : a ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hc : (-Complex.I)-Complex.I = -a := by dsimp [a]; ring
  have hsign : ((-a)^Fintype.card I)^2 = (a^Fintype.card I)^2 := by
    calc
      _ = ((-a)^2)^Fintype.card I := pow_right_comm _ _ _
      _ = (a^2)^Fintype.card I := by rw [neg_sq]
      _ = _ := pow_right_comm _ _ _
  have hP : ((complexPeriods P Q).det)^2 = (a^Fintype.card I*G.det)^2 := by
    have hh := congrArg Matrix.det (bilinear_blocks P Q h)
    simp only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_fromBlocks_zero₂₁] at hh
    have he : (complexPeriods P Q).det^2 * (standardJ (I:=I)).det^2 =
        (mixedPairing P Q).det^2 := by
      simpa only [pow_two,mul_assoc,mul_left_comm,mul_comm] using hh
    rw [j_det_sq,mul_one,hG,Matrix.det_smul] at he
    exact he
  let d : ℂ := ((groupedReal P Q).det : ℂ)
  have hleft : (complexPeriods P Q).det^2 = (a^Fintype.card I)^2 * d^2 := by
    calc
      _ = ((-a)^Fintype.card I * d)^2 := by rw [complex_det,hc]
      _ = ((-a)^Fintype.card I)^2 * d^2 := mul_pow _ _ _
      _ = _ := congrArg (fun z : ℂ => z*d^2) hsign
  have hright : (a^Fintype.card I * G.det)^2 =
      (a^Fintype.card I)^2 * G.det^2 := mul_pow _ _ _
  have hcancel : (a^Fintype.card I)^2 * d^2 = (a^Fintype.card I)^2 * G.det^2 :=
    hleft.symm.trans (hP.trans hright)
  have hs : d^2 = G.det^2 :=
    mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero (Fintype.card I) ha)) hcancel
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hp|hp
  · have hv : (groupedReal P Q).det=G.det.re := by
      simpa only [d,Complex.ofReal_re] using congrArg Complex.re hp
    rw [hv,abs_of_pos hpos]
  · have hv : (groupedReal P Q).det= -G.det.re := by
      simpa only [d,Complex.ofReal_re,Complex.neg_re] using congrArg Complex.re hp
    rw [hv,abs_neg,abs_of_pos hpos]

end OriginalSameJSymplecticPeriods318

#print axioms OriginalSameJSymplecticPeriods318.whole_complexification
#print axioms OriginalSameJSymplecticPeriods318.bilinear_blocks
#print axioms OriginalSameJSymplecticPeriods318.actual_determinant
