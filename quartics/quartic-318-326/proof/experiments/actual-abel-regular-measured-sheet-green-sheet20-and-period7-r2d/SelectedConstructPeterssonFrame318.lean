module
public import SelectedGammaOneQuotientArea318
public import SelectedWeightTwoPetersson318
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public section
noncomputable section

open Matrix Unitary MeasureTheory UpperHalfPlane
open scoped BigOperators ComplexOrder ComplexConjugate Classical Matrix
open SelectedGammaOneQuotientArea318 SelectedWeightTwoPetersson318
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318

namespace SelectedConstructPeterssonFrame318

/-- Positive definiteness on the actual ordered Gram determines an
invertible orthonormalizing coordinate matrix. No orthonormal frame
is manufactured by assuming a desired inverse relation. -/
theorem normalize_positive_gram {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ)
    (hG : Matrix.PosDef G) :
    ∃ Z : Matrix (Fin g) (Fin g) ℂ, IsUnit Z ∧ Zᴴ * G * Z = 1 := by
  let h := hG.isHermitian
  let U : Matrix (Fin g) (Fin g) ℂ := h.eigenvectorUnitary
  let eig := fun j => h.eigenvalues j
  let q := fun j => ((Real.sqrt (eig j))⁻¹ : ℝ)
  let D : Matrix (Fin g) (Fin g) ℂ := Matrix.diagonal (fun j => Complex.ofReal (q j))
  let Λ : Matrix (Fin g) (Fin g) ℂ := Matrix.diagonal (fun j => Complex.ofReal (eig j))
  let Z := U*D
  have hd : Uᴴ * G * U = Λ := by
    have hh := h.conjStarAlgAut_star_eigenvectorUnitary
    rw [conjStarAlgAut_star_apply] at hh
    simpa only [U, Λ, eig, Matrix.star_eq_conjTranspose, RCLike.ofReal_eq_complex_ofReal,
      mul_assoc, Function.comp_def] using hh
  have hD : Dᴴ = D := by
    ext r c
    by_cases hrc : r=c
    · subst c
      simp [D, Matrix.conjTranspose_apply]
    · unfold D
      rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ (Ne.symm hrc),
        Matrix.diagonal_apply_ne _ hrc, star_zero]
  have h₁ : D * Λ * D = 1 := by
    rw [show D = Matrix.diagonal (fun j => Complex.ofReal (q j)) from rfl]
    rw [show Λ = Matrix.diagonal (fun j => Complex.ofReal (eig j)) from rfl]
    rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    ext r c
    by_cases hrc : r=c
    · subst c
      rw [Matrix.diagonal_apply_eq,Matrix.one_apply_eq]
      have hpos : 0 < eig r := hG.eigenvalues_pos r
      have hs : Real.sqrt (eig r) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
      have hR : (q r * eig r) * q r = 1 := by
        dsimp only [q]
        field_simp [hs] <;> nlinarith [Real.sq_sqrt hpos.le]
      simp only [← Complex.ofReal_mul,hR,Complex.ofReal_one]
    · rw [Matrix.diagonal_apply_ne _ hrc, Matrix.one_apply_ne hrc]
  have hZ : Zᴴ * G * Z = 1 := by
    calc
      _ = D * (Uᴴ * G * U) * D := by
        unfold Z
        rw [Matrix.conjTranspose_mul,hD]
        noncomm_ring
      _ = 1 := by rw [hd,h₁]
  refine ⟨Z,(Matrix.isUnit_iff_isUnit_det Z).mpr (isUnit_iff_ne_zero.mpr ?_),hZ⟩
  intro hz
  have he := congrArg Matrix.det hZ
  exact zero_ne_one (by simpa only [Matrix.det_mul,hz,mul_zero,Matrix.det_one] using he)

variable {M g : ℕ}
variable (h5 : 5 ≤ M) (f : Fin g → Form M)

/-- The ordered Gram on the literal quotient measure, in the same
order used by the algebraic ordinary evaluations. -/
def originalGram : Matrix (Fin g) (Fin g) ℂ :=
  fun i j => ∫ q, cross (f i) (f j) q ∂(area M h5)

/-- An explicit linear combination of the original forms, not
a second independently chosen list of holomorphic differentials. -/
def reframe (Z : Matrix (Fin g) (Fin g) ℂ) (j : Fin g) : Form M :=
  ∑ i, Z i j • f i

private def evalAt {N : ℕ} (τ : UpperHalfPlane) : Form N →ₗ[ℂ] ℂ where
  toFun f := f τ
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

theorem reframe_apply (Z : Matrix (Fin g) (Fin g) ℂ) (j : Fin g) (τ : UpperHalfPlane) :
    reframe f Z j τ = ∑ i, Z i j * f i τ := by
  change evalAt τ (∑ i, Z i j • f i) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul]
  rfl

private theorem cross_reframe (Z : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g)
    (q : Base (image M)) :
    cross (reframe f Z i) (reframe f Z j) q =
      ∑ r, ∑ c, (conj (Z r i) * Z c j) * cross (f r) (f c) q := by
  obtain ⟨τ,rfl⟩ := GammaOneAtlas318.quotient_surjective M q
  simp only [cross_projection,reframe_apply,map_sum,map_mul]
  simp only [Finset.sum_mul,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun c _ => ?_))
  ring

theorem measured_gram_reframe (Z : Matrix (Fin g) (Fin g) ℂ)
    (integrable : ∀ i j, Integrable (cross (f i) (f j)) (area M h5)) (i j : Fin g) :
    Integrable (cross (reframe f Z i) (reframe f Z j)) (area M h5) ∧
      (∫ q, cross (reframe f Z i) (reframe f Z j) q ∂(area M h5)) =
        (Zᴴ * originalGram h5 f * Z) i j := by
  have hp (r c : Fin g) :
      Integrable (fun q => (conj (Z r i) * Z c j) * cross (f r) (f c) q) (area M h5) :=
    (integrable r c).const_mul _
  have hr (r : Fin g) :
      Integrable (fun q => ∑ c, (conj (Z r i) * Z c j) * cross (f r) (f c) q) (area M h5) :=
    integrable_finsetSum _ (fun c _ => hp r c)
  have hrow (r : Fin g) :
      (∫ q, ∑ c, (conj (Z r i) * Z c j) * cross (f r) (f c) q ∂(area M h5)) =
        ∑ c, (conj (Z r i) * Z c j) * originalGram h5 f r c := by
    rw [integral_finsetSum _ (fun c _ => hp r c)]
    simp only [integral_const_mul, originalGram]
  rw [funext (cross_reframe f Z i j)]
  refine ⟨integrable_finsetSum _ (fun r _ => hr r),?_⟩
  rw [integral_finsetSum _ (fun r _ => hr r)]
  simp_rw [hrow]
  calc
    _ = ∑ c, ∑ r, (conj (Z r i) * Z c j) * originalGram h5 f r c := Finset.sum_comm
    _ = _ := ?_
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.sum_mul,starRingEnd_apply]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun r _ => ?_))
  ring

/-- For the SAME ordered regular cusp forms, the actual Gram
produces the exact normalized pairwise integrals consumed by
the inverse-disk estimate. -/
theorem actual_orthonormal_frame (integrable : ∀ i j,
    Integrable (cross (f i) (f j)) (area M h5)) (positive : PosDef (originalGram h5 f)) :
    ∃ Z : Matrix (Fin g) (Fin g) ℂ, IsUnit Z ∧
      Zᴴ * originalGram h5 f * Z = 1 ∧
      (∀ i j, Integrable (cross (reframe f Z i) (reframe f Z j)) (area M h5)) ∧
      ∀ i j, (∫ q, cross (reframe f Z i) (reframe f Z j) q ∂(area M h5)) =
        if i = j then 1 else 0 := by
  obtain ⟨Z,hunit,hZ⟩ := normalize_positive_gram _ positive
  refine ⟨Z,hunit,hZ,fun i j => (measured_gram_reframe h5 f Z integrable i j).1,?_⟩
  intro i j
  rw [(measured_gram_reframe h5 f Z integrable i j).2,hZ,Matrix.one_apply]

end SelectedConstructPeterssonFrame318

#print axioms SelectedConstructPeterssonFrame318.normalize_positive_gram
#print axioms SelectedConstructPeterssonFrame318.actual_orthonormal_frame
