module
public import SelectedOriginalAbelSumGramIntegral318
public import SelectedAbelFiniteSheetMeasure318
import Mathlib.Tactic.Ring
public section
noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ENNReal NNReal Classical ComplexConjugate
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedWeightTwoPetersson318 SelectedGammaOneQuotientArea318
open SelectedAbelSumGramProductIntegral318 SelectedOriginalAbelSumGramIntegral318
open SelectedAbelFiniteSheetMeasure318

namespace SelectedOriginalAbelMeasuredCover318

private theorem measurable_sum' {ι X : Type*} [MeasurableSpace X]
    (s : Finset ι) (u : ι → X → ℂ) (h : ∀ i, Measurable (u i)) :
    Measurable (fun x => ∑ i ∈ s, u i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (measurable_const : Measurable (fun _ : X => (0 : ℂ)))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i).add ih

private theorem measurable_prod' {ι X : Type*} [MeasurableSpace X]
    (s : Finset ι) (u : ι → X → ℂ) (h : ∀ i, Measurable (u i)) :
    Measurable (fun x => ∏ i ∈ s, u i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (measurable_const : Measurable (fun _ : X => (1 : ℂ)))
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i).mul ih

/-- Pointwise density in actual product coordinates, before any
integration. This is the signed Leibniz expansion of the square norm
of the complex determinant, with the conjugate index first. -/
theorem expanded_density {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) :
    (∑ s : Equiv.Perm (Fin g), ∑ t : Equiv.Perm (Fin g),
      (rsign ℂ s * rsign ℂ t) * ∏ k, (conj (A (s k) k) * A (t k) k)) =
        (Complex.normSq A.det : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Matrix.det_apply', map_sum, map_mul, map_prod, map_intCast]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib]
  ring

variable {M g : ℕ} (f : Fin g → Form M)

abbrev Domain (M g : ℕ) := Fin g → Base (image M)

/-- The very same density already integrated in the original product
Gram lemma, on the actual modular quotient and fixed ordered forms. -/
abbrev complexDensity (z : Domain M g) : ℂ :=
  ∑ s : Equiv.Perm (Fin g), ∑ t : Equiv.Perm (Fin g),
    summand (fun i j => cross (f i) (f j)) s t z

def positiveDensity (z : Domain M g) : ℝ≥0 :=
  (complexDensity f z).re.toNNReal

theorem image_of_positiveDensity (z : Domain M g) :
    complexDensity f z = ((positiveDensity f z : ℝ) : ℂ) := by
  let τ : Fin g → UpperHalfPlane :=
    fun k => Classical.choose (GammaOneAtlas318.quotient_surjective M (z k))
  have ht (k : Fin g) : quotientMap M (τ k) = z k :=
    Classical.choose_spec (GammaOneAtlas318.quotient_surjective M (z k))
  let A : Matrix (Fin g) (Fin g) ℂ := fun i k => f i (τ k) * ((τ k).im : ℂ)
  have hc (i j k : Fin g) : cross (f i) (f j) (z k) = conj (A i k) * A j k := by
    rw [←ht k, cross_projection]
    simp only [A, map_mul, Complex.conj_ofReal]
    ring
  have hA : complexDensity f z = (Complex.normSq A.det : ℂ) := by
    unfold complexDensity summand
    simp_rw [hc]
    exact expanded_density A
  unfold positiveDensity
  rw [hA, Complex.ofReal_re, Real.coe_toNNReal _ (Complex.normSq_nonneg _)]

theorem positiveDensity_measurable : Measurable (positiveDensity f) := by
  have hcross (i j : Fin g) : Measurable (cross (f i) (f j)) := by
    apply measurable_from_quotient.mpr
    change Measurable (UpperHalfPlane.petersson 2 (fun q => f i q) (fun q => f j q))
    exact (UpperHalfPlane.petersson_continuous _ (ModularFormClass.continuous (f i))
      (ModularFormClass.continuous (f j))).measurable
  have h : Measurable (complexDensity f) := by
    unfold complexDensity
    apply measurable_sum' _ _ (fun s => ?_)
    apply measurable_sum' _ _ (fun t => ?_)
    unfold summand
    apply measurable_const.mul
    exact measurable_prod' _ _ (fun k => (hcross (s k) (t k)).comp (measurable_pi_apply k))
  exact (Complex.continuous_re.measurable.comp h).real_toNNReal

variable (h5 : 5 ≤ M)

abbrev productArea : Measure (Domain M g) := Measure.pi (fun _ : Fin g => area M h5)
abbrev pullbackVolume : Measure (Domain M g) :=
  (productArea (g:=g) h5).withDensity (fun z => (positiveDensity f z : ℝ≥0∞))

/-- Replace the former single global Abel-volume premise by the
literal finite sheets and their local geometric change of variables.
The determinant density is constructed measurably from the original
ordered forms and the original quotient measure; it is not provided. -/
theorem hcover_of_actual_sheets {Y : Type*} [MeasurableSpace Y]
    (a : Domain M g → Y) (ha : Measurable a) (ν : Measure Y)
    (U : ℕ → Set Y) (hU : ∀ j, MeasurableSet (U j))
    (S : ℕ → Fin g.factorial → Set (Domain M g))
    (hS : ∀ j k, MeasurableSet (S j k))
    (disjoint : ∀ j, Pairwise (fun k l => Disjoint (S j k) (S j l)))
    (preimage : ∀ j, (⋃ k, S j k) = a ⁻¹' U j)
    (sheet : ∀ j k, Measure.map a ((pullbackVolume f h5).restrict (S j k)) = ν.restrict (U j))
    (nullSrc : pullbackVolume f h5 (a ⁻¹' (⋃ j, U j)ᶜ) = 0)
    (nullDst : ν (⋃ j, U j)ᶜ = 0) :
    (g.factorial : ℂ) * ((ν univ).toReal : ℂ) = originalVolumeIntegral h5 f := by
  have hh := map_eq_count_of_ae_sheets ha (pullbackVolume f h5) ν U hU S hS
    disjoint preimage sheet nullSrc nullDst
  have hD : complexDensity f =ᵐ[productArea (g:=g) h5]
      fun x => (((positiveDensity f x : ℝ)) : ℂ) :=
    Filter.Eventually.of_forall (image_of_positiveDensity f)
  exact (complex_integral_eq_count_of_density ha ν (productArea (g:=g) h5)
    (positiveDensity f) (positiveDensity_measurable f) (complexDensity f) hD hh).symm

end SelectedOriginalAbelMeasuredCover318

#print axioms SelectedOriginalAbelMeasuredCover318.image_of_positiveDensity
#print axioms SelectedOriginalAbelMeasuredCover318.hcover_of_actual_sheets
