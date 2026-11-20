module
public import ActualWronskian318
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Tactic
public section
noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators

namespace SelectedOneDiskHadamard318

/-- Complex Hadamard for the actual evaluation matrix. Its rows carry the
Euclidean norm, not the default sup norm on a function type. The extending
Gram–Schmidt basis also covers singular matrices. -/
theorem det_le_rows {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) :
    ‖A.det‖ ≤ ∏ i : Fin g, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin g))‖ := by
  classical
  let rows : Fin g → EuclideanSpace ℂ (Fin g) := fun i => WithLp.toLp 2 (A i)
  let b := EuclideanSpace.basisFun (Fin g) ℂ
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin g)) = Fintype.card (Fin g) :=
    finrank_euclideanSpace
  let e := InnerProductSpace.gramSchmidtOrthonormalBasis hdim rows
  have hmat : b.toBasis.toMatrix rows = A.transpose := by
    ext i j
    change b.toBasis.repr (rows j) i = A j i
    simp only [OrthonormalBasis.coe_toBasis_repr_apply, b, EuclideanSpace.basisFun_repr,
      rows, PiLp.toLp_apply]
  have hchange : b.toBasis.det rows = (b.toBasis.det e) * e.toBasis.det rows := by
    have h := congrArg (fun d => d rows)
      (AlternatingMap.eq_smul_basis_det e.toBasis b.toBasis.det)
    simpa only [smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis] using h
  have hdiag : e.toBasis.det rows = ∏ i, inner ℂ (e i) (rows i) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hdim rows
  change ‖A.det‖ ≤ ∏ i, ‖rows i‖
  calc
    ‖A.det‖ = ‖b.toBasis.det rows‖ := by
      rw [Module.Basis.det_apply, hmat, Matrix.det_transpose]
    _ = ‖e.toBasis.det rows‖ := by
      rw [hchange, norm_mul, OrthonormalBasis.det_to_matrix_orthonormalBasis, one_mul]
    _ = ∏ i, ‖inner ℂ (e i) (rows i)‖ := by rw [hdiag, norm_prod]
    _ ≤ ∏ i, ‖rows i‖ := by
      refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => ?_)
      simpa only [e.norm_eq_one, one_mul] using norm_inner_le_norm (𝕜 := ℂ) (e i) (rows i)

/-- A bound on all unit-combination values bounds the Euclidean row norm.
The maximizing coefficient vector is the normalized conjugate row. -/
theorem row_le_of_unit {g : ℕ} (a : Fin g → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ x : EuclideanSpace ℂ (Fin g), ‖x‖ = 1 → ‖∑ j, x j * a j‖ ≤ R) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℂ (Fin g))‖ ≤ R := by
  let w : EuclideanSpace ℂ (Fin g) := WithLp.toLp 2 (fun j => star (a j))
  have hw_eq : ‖(WithLp.toLp 2 a : EuclideanSpace ℂ (Fin g))‖ = ‖w‖ := by
    rw [EuclideanSpace.norm_eq (WithLp.toLp 2 a), EuclideanSpace.norm_eq w]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    change ‖a j‖ ^ 2 = ‖star (a j)‖ ^ 2
    rw [RCLike.star_def, RCLike.norm_conj]
  rw [hw_eq]
  by_cases hw : w = 0
  · rw [hw, norm_zero]
    exact hR
  · have h0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    have h0' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast h0
    let x : EuclideanSpace ℂ (Fin g) := (‖w‖ : ℂ)⁻¹ • w
    have hx : ‖x‖ = 1 := by
      dsimp only [x]
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg w), inv_mul_cancel₀ h0]
    have hs : inner ℂ w x = ∑ j, x j * a j := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro j _
      change inner ℂ (star (a j)) (x j) = x j * a j
      rw [RCLike.inner_apply, ← RCLike.star_def, star_star]
    have hi : inner ℂ w x = (‖w‖ : ℂ) := by
      dsimp only [x]
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
      let z : ℂ := (‖w‖ : ℂ)
      have hz : z ≠ 0 := h0'
      change z⁻¹ * z ^ 2 = z
      calc
        z⁻¹ * z ^ 2 = (z⁻¹ * z) * z := by ring
        _ = z := by rw [inv_mul_cancel₀ hz, one_mul]
    have hb := h x hx
    rw [← hs, hi, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg w)] at hb
    exact hb

def combination {g : ℕ} (f : Fin g → ℂ → ℂ) (x : EuclideanSpace ℂ (Fin g))
    (z : ℂ) : ℂ := ∑ j, x j * f j z

/-- One fixed square minor of the actual ordinary j=1 evaluation map.
Local energy is for every unit combination of the *same* basis, not
only one basis vector at a time. No determinant estimate is an input. -/
theorem logdet {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ)
    (f : Fin g → Fin g → ℂ → ℂ) (eval : ∀ i j, A i j = f i j 0)
    (hf : ∀ i x, ‖x‖ = 1 → DifferentiableOn ℂ (combination (f i) x) (ball 0 1))
    (hi : ∀ i x, ‖x‖ = 1 → IntegrableOn (fun z => ‖combination (f i) x z‖ ^ 2) (ball 0 1))
    (he : ∀ i x, ‖x‖ = 1 → (∫ z in ball (0 : ℂ) 1, ‖combination (f i) x z‖ ^ 2) ≤ 1)
    (hnz : A.det ≠ 0) :
    Real.log ‖A.det‖ ≤ -(g : ℝ) * (Real.log Real.pi / 2) := by
  let R := Real.sqrt (1 / Real.pi)
  have hR : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hrows (i : Fin g) :
      ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin g))‖ ≤ R := by
    apply row_le_of_unit (A i) hR.le
    intro x hx
    have hc := ActualWronskian318.local_coefficient (combination (f i) x) 0 1
      (by norm_num) (hf i x hx) (hi i x hx) (he i x hx) 0
    have heq : (∑ j, x j * A i j) = combination (f i) x 0 := by
      simp only [combination, eval]
    rw [heq]
    simpa [R] using hc
  have hprod : (∏ i : Fin g, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin g))‖) ≤ R^g := by
    calc
      _ ≤ ∏ _i : Fin g, R :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hrows i)
      _ = _ := by simp
  have hlog := Real.log_le_log (norm_pos_iff.mpr hnz) ((det_le_rows A).trans hprod)
  have hrlog : Real.log R = -(Real.log Real.pi / 2) := by
    change Real.log (Real.sqrt (1 / Real.pi)) = _
    rw [Real.log_sqrt (by positivity), Real.log_div one_ne_zero Real.pi_pos.ne', Real.log_one]
    ring
  rw [Real.log_pow, hrlog] at hlog
  simpa only [mul_neg, neg_mul] using hlog

/-- Archimedean cancellation on the normalized determinant degree of
this minor. The finite scalar losses do not reverse the upper bound. -/
theorem shift_cancel {g : ℕ} (F : Fin g → ℝ) (a loss arch h0 hplus : ℝ)
    (hF : ∀ i, F i ≤ a) (hl : 0 ≤ loss)
    (hev : h0 = (∑ i, F i) - loss + arch)
    (harch : arch ≤ -(g : ℝ) * (Real.log Real.pi / 2))
    (hshift : hplus = h0 + (g : ℝ) * (Real.log Real.pi / 2)) :
    hplus ≤ (g : ℝ) * a := by
  have hsum : (∑ i, F i) ≤ (g : ℝ) * a := by
    calc
      _ ≤ ∑ _i : Fin g, a := Finset.sum_le_sum fun i _ => hF i
      _ = _ := by simp
  linarith

end SelectedOneDiskHadamard318
#print axioms SelectedOneDiskHadamard318.det_le_rows
#print axioms SelectedOneDiskHadamard318.logdet
#print axioms SelectedOneDiskHadamard318.shift_cancel
