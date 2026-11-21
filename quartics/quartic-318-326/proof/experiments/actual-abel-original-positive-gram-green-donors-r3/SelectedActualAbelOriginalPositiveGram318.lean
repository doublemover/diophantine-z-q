module

public import SelectedActualGammaOneAreaFullSupport318
public import SelectedGammaOneFinitePetersson318
public import SelectedConstructPeterssonFrame318
import all SelectedConstructPeterssonFrame318
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

public section

noncomputable section

open Function Set MeasureTheory Matrix UpperHalfPlane
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedGammaOneQuotientArea318 SelectedWeightTwoPetersson318
open SelectedConstructPeterssonFrame318 SelectedGammaOneFinitePetersson318
open SelectedActualGammaOneAreaFullSupport318
open scoped BigOperators ComplexOrder ComplexConjugate Matrix

namespace SelectedActualAbelOriginalPositiveGram318

variable {M g : ℕ}

private theorem cross_conjugate (F G : Form M) (z : Base (image M)) :
    conj (cross F G z) = cross G F z := by
  obtain ⟨t,rfl⟩ := quotient_surjective M z
  simp only [cross_projection,map_mul,map_pow,Complex.conj_conj,Complex.conj_ofReal]
  ring

private theorem cross_diagonal (F : Form M) (t : UpperHalfPlane) :
    cross F F (quotientMap M t) = Complex.ofReal ((‖F t‖ ^ 2) * t.im ^ 2) := by
  rw [cross_projection, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul]

private theorem original_cross_positive (hM : 5 ≤ M) (F : Form M) (hF : F ≠ 0) :
    (0 : ℂ) < ∫ z, cross F F z ∂(area M hM) := by
  let μ := area M hM
  letI : Measure.IsOpenPosMeasure μ := actual_area_open_positive M hM
  let u : Base (image M) → ℝ := fun z => (cross F F z).re
  have hcross : Continuous (cross F F) := by
    apply continuous_quot_lift
    exact UpperHalfPlane.petersson_continuous _
      (ModularFormClass.continuous F) (ModularFormClass.continuous F)
  have huc : Continuous u := Complex.continuous_re.comp hcross
  have hui : Integrable u μ := by
    change Integrable (Complex.reCLM ∘ cross F F) μ
    exact Complex.reCLM.integrable_comp (cross_integrable M hM F F)
  have hread (t : UpperHalfPlane) : u (quotientMap M t) = (‖F t‖ ^ 2) * t.im ^ 2 := by
    change (cross F F (quotientMap M t)).re = _
    rw [cross_diagonal,Complex.ofReal_re]
  have hu : 0 ≤ u := by
    intro z
    obtain ⟨t,rfl⟩ := quotient_surjective M z
    change 0 ≤ u (quotientMap M t)
    rw [hread]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  obtain ⟨t,ht⟩ : ∃ t : UpperHalfPlane, F t ≠ 0 := by
    by_contra! hz
    apply hF
    exact DFunLike.ext _ _ (fun t => by simpa using hz t)
  have htu : u (quotientMap M t) ≠ 0 := by
    rw [hread]
    exact mul_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)) (pow_ne_zero 2 t.im_ne_zero)
  have hpos : 0 < ∫ z, u z ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero huc hui hu htu
  have heq (z : Base (image M)) : cross F F z = Complex.ofReal (u z) := by
    obtain ⟨v,rfl⟩ := quotient_surjective M z
    rw [cross_diagonal,hread]
  change (0 : ℂ) < ∫ z, cross F F z ∂μ
  simp_rw [heq]
  rw [integral_complex_ofReal]
  exact Complex.zero_lt_real.2 hpos

/-- The exact original Petersson Gram of any independent ordered
weight-two cusp frame is positive definite. Both the conjugate-first
orientation and the positive mass use the same original quotient and
canonical measure; no auxiliary Gram or positivity hypothesis. -/
theorem original_gram_posDef (hM : 5 ≤ M) (f : Fin g → Form M)
    (hf : LinearIndependent ℂ f) : (originalGram hM f).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change (originalGram hM f)ᴴ = originalGram hM f
    ext i j
    rw [Matrix.conjTranspose_apply]
    change conj (∫ z, cross (f j) (f i) z ∂(area M hM)) =
      ∫ z, cross (f i) (f j) z ∂(area M hM)
    have h := (integral_conj (μ := area M hM) (f := cross (f j) (f i))).symm
    simp_rw [cross_conjugate] at h
    exact h
  · intro x hx
    obtain ⟨j,hj⟩ : ∃ j : Fin g, x j ≠ 0 := by
      by_contra! h
      apply hx
      funext i
      exact h i
    let Z : Matrix (Fin g) (Fin g) ℂ := fun i _ => x i
    let F := reframe f Z j
    have hF : F ≠ 0 := by
      intro hz
      have hsum : (∑ i, x i • f i) = 0 := by
        simpa only [F,reframe,Z] using hz
      exact hj ((Fintype.linearIndependent_iff.mp hf) x hsum j)
    have hInt : (∫ z, cross F F z ∂(area M hM)) =
        (Zᴴ * originalGram hM f * Z) j j :=
      (measured_gram_reframe hM f Z (fun i j => cross_integrable M hM (f i) (f j)) j j).2
    have hdot : (Zᴴ * originalGram hM f * Z) j j =
        star x ⬝ᵥ (originalGram hM f *ᵥ x) := by
      rw [Matrix.mul_assoc]
      simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.mulVec,dotProduct,
        Pi.star_apply,Z]
    rw [←hdot,←hInt]
    exact original_cross_positive hM F hF

/-- Consequently the already verified normalization uses the same
independent actual frame and needs no supplied analytic norm premise. -/
theorem actual_orthonormal_frame_of_independent (hM : 5 ≤ M)
    (f : Fin g → Form M) (hf : LinearIndependent ℂ f) :
    ∃ Z : Matrix (Fin g) (Fin g) ℂ, IsUnit Z ∧
      Zᴴ * originalGram hM f * Z = 1 ∧
      (∀ i j, Integrable (cross (reframe f Z i) (reframe f Z j)) (area M hM)) ∧
      ∀ i j, (∫ q, cross (reframe f Z i) (reframe f Z j) q ∂(area M hM)) =
        if i = j then 1 else 0 := by
  classical
  exact actual_orthonormal_frame hM f
    (fun i j => cross_integrable M hM (f i) (f j)) (original_gram_posDef hM f hf)

end SelectedActualAbelOriginalPositiveGram318

#print axioms SelectedActualAbelOriginalPositiveGram318.original_gram_posDef
#print axioms SelectedActualAbelOriginalPositiveGram318.actual_orthonormal_frame_of_independent
