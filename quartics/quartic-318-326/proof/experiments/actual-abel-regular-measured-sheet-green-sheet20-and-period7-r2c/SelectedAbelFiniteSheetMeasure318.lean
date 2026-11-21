module
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace SelectedAbelFiniteSheetMeasure318

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {a : X → Y} (ha : Measurable a) (μ : Measure X) (ν : Measure Y)
variable {d : ℕ}

include ha in
/-- One evenly covered measurable target patch. Count the given
disjoint sheets, each with its literal change-of-variables measure. -/
theorem map_restrict_eq_count {U : Set Y} (hU : MeasurableSet U)
    (S : Fin d → Set X) (hS : ∀ k, MeasurableSet (S k))
    (disjoint : Pairwise (fun k l => Disjoint (S k) (S l)))
    (preimage : (⋃ k, S k) = a ⁻¹' U)
    (sheet : ∀ k, Measure.map a (μ.restrict (S k)) = ν.restrict U) :
    (Measure.map a μ).restrict U = ((d : ℝ≥0∞) • ν).restrict U := by
  ext1 t ht
  rw [Measure.restrict_map ha hU, Measure.map_apply ha ht, ←preimage]
  rw [Measure.restrict_iUnion_apply disjoint hS (ha ht),
    Measure.restrict_smul, Measure.smul_apply]
  have he (k : Fin d) : μ.restrict (S k) (a ⁻¹' t) = ν.restrict U t :=
    (Measure.map_apply ha ht).symm.trans (congrArg (fun m : Measure Y => m t) (sheet k))
  simp only [he, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, smul_eq_mul]

include ha in
/-- Global covering measure on a countable atlas, discarding only the
two specified null complements. This does not require the cover to
extend across a ramification or exceptional locus. -/
theorem map_eq_count_of_ae_sheets
    (U : ℕ → Set Y) (hU : ∀ j, MeasurableSet (U j))
    (S : ℕ → Fin d → Set X) (hS : ∀ j k, MeasurableSet (S j k))
    (disjoint : ∀ j, Pairwise (fun k l => Disjoint (S j k) (S j l)))
    (preimage : ∀ j, (⋃ k, S j k) = a ⁻¹' U j)
    (sheet : ∀ j k, Measure.map a (μ.restrict (S j k)) = ν.restrict (U j))
    (nullSrc : μ (a ⁻¹' (⋃ j, U j)ᶜ) = 0)
    (nullDst : ν (⋃ j, U j)ᶜ = 0) :
    Measure.map a μ = (d : ℝ≥0∞) • ν := by
  let V := ⋃ j, U j
  have hv : MeasurableSet V := MeasurableSet.iUnion hU
  have hfirst : ∀ᵐ y ∂(Measure.map a μ), y ∈ V := by
    rw [ae_iff]
    change (Measure.map a μ) Vᶜ = 0
    rw [Measure.map_apply ha hv.compl]
    exact nullSrc
  have hsecond : ∀ᵐ y ∂((d : ℝ≥0∞) • ν), y ∈ V := by
    rw [ae_iff]
    change ((d : ℝ≥0∞) • ν) Vᶜ = 0
    rw [Measure.smul_apply, show ν Vᶜ = 0 from nullDst, smul_zero]
  have hloc (j : ℕ) :
      (Measure.map a μ).restrict (U j) = ((d : ℝ≥0∞) • ν).restrict (U j) :=
    map_restrict_eq_count ha μ ν (hU j) (S j) (hS j) (disjoint j) (preimage j) (sheet j)
  have hfull : (Measure.map a μ).restrict V = ((d : ℝ≥0∞) • ν).restrict V :=
    (Measure.restrict_iUnion_congr (s := U)).mpr hloc
  exact (Measure.restrict_eq_self_of_ae_mem hfirst).symm.trans
    (hfull.trans (Measure.restrict_eq_self_of_ae_mem hsecond))

include ha in
/-- The actual Abel comparison uses complex-valued bookkeeping for the
finite Gram expansion but the area is positive. If its integrand is
the real pullback density a.e., the exact degree count holds natively
for the integral, without postulating the global integral equality. -/
theorem complex_integral_eq_count_of_density
    (μ₀ : Measure X) (w : X → ℝ≥0) (hw : Measurable w)
    (u : X → ℂ) (hu : u =ᵐ[μ₀] fun x => ((w x : ℝ) : ℂ))
    (hmap : Measure.map a (μ₀.withDensity fun x => (w x : ℝ≥0∞)) =
      (d : ℝ≥0∞) • ν) :
    (∫ x, u x ∂μ₀) = (d : ℂ) * ((ν univ).toReal : ℂ) := by
  let m := μ₀.withDensity fun x => (w x : ℝ≥0∞)
  have hm : m univ = (d : ℝ≥0∞) * ν univ := by
    have h := congrArg (fun q : Measure Y => q univ) hmap
    rw [Measure.map_apply ha MeasurableSet.univ, Set.preimage_univ,
      Measure.smul_apply, smul_eq_mul] at h
    exact h
  have hconst : (∫ _x : X, (1 : ℂ) ∂m) = ((m univ).toReal : ℂ) := by
    simp only [integral_const, Complex.real_smul, mul_one, measureReal_def]
  calc
    (∫ x, u x ∂μ₀) = ∫ x, (w x) • (1 : ℂ) ∂μ₀ := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [hx]
      change ((w x : ℝ) : ℂ) = (w x : ℝ) • (1 : ℂ)
      rw [Complex.real_smul]
      exact (mul_one _).symm
    _ = ∫ _x : X, (1 : ℂ) ∂m :=
      (integral_withDensity_eq_integral_smul hw (fun _ : X => (1 : ℂ))).symm
    _ = (d : ℂ) * ((ν univ).toReal : ℂ) := by
      rw [hconst, hm, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        Complex.ofReal_mul, Complex.ofReal_natCast]

end SelectedAbelFiniteSheetMeasure318

#print axioms SelectedAbelFiniteSheetMeasure318.map_restrict_eq_count
#print axioms SelectedAbelFiniteSheetMeasure318.map_eq_count_of_ae_sheets
#print axioms SelectedAbelFiniteSheetMeasure318.complex_integral_eq_count_of_density
