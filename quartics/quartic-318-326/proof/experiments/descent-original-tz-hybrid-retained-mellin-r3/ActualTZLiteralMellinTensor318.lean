module
public import ActualTZLiteralSchwartz318
public section
noncomputable section
namespace ActualTZLiteralMellinTensor318
open MeasureTheory
open scoped BigOperators
open ActualTZMellinKernel318 ActualTZLiteralSchwartz318

variable {I : Type*} [Fintype I]
abbrev Slot (I : Type*) := I × Bool
abbrev Digits (I : Type*) := Slot I → ℕ

@[expose] def μ (I : Type*) [Fintype I] : Measure (Slot I→ℝ) :=
  Measure.pi fun _ => volume

@[expose] def spectral (C : Cutoff) (L : ℝ) (d : ℕ) (ξ : ℝ) : ℂ :=
  φ C ξ*(d:ℂ)^(-(mode ξ/(L:ℂ)))

private theorem regulator_re (L ξ : ℝ) :
    (-(mode ξ/(L:ℂ))).re = -(1/L) := by
  rw [Complex.neg_re,Complex.div_ofReal_re,mode_re]

theorem spectral_norm (C : Cutoff) (L : ℝ) (d : ℕ) (hd : 0<d) (ξ : ℝ) :
    ‖spectral C L d ξ‖=‖φ C ξ‖*(d:ℝ)^(-(1/L)) := by
  rw [spectral,norm_mul,Complex.norm_natCast_cpow_of_pos hd,regulator_re]

private theorem spectral_integrable (C : Cutoff) (L : ℝ) (d : ℕ) (hd : 0<d) :
    Integrable (spectral C L d) := by
  have H : Continuous mode := by unfold mode; fun_prop
  have hdom : Integrable (fun ξ => ‖φ C ξ‖*(d:ℝ)^(-(1/L))) :=
    (φ_integrable C).norm.mul_const _
  have hdC : (d:ℂ)≠0 := by exact_mod_cast hd.ne'
  have hC : Continuous (spectral C L d) := by
    unfold spectral
    simp only [Complex.cpow_def_of_ne_zero hdC]
    fun_prop
  apply hdom.mono' hC.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => (spectral_norm C L d hd ξ).le

@[expose] def rowProduct (C : Cutoff) (L : ℝ) (d : Digits I) (ξ : Slot I→ℝ) : ℂ :=
  ∏ j : Slot I,spectral C L (d j) (ξ j)

theorem rowProduct_integrable (C : Cutoff) (L : ℝ) (d : Digits I) (hd : ∀ j,0<d j) :
    Integrable (rowProduct C L d) (μ I) :=
  Integrable.fintype_prod (fun j : Slot I => spectral_integrable C L (d j) (hd j))

/-- Both divisor slots at original i are separate angular
coordinates, but they evaluate the same cutoff function. -/
theorem rowProduct_integral (C : Cutoff) (L : ℝ) (hL : 0<L) (d : Digits I)
    (hd : ∀ j,0<d j) :
    (∫ ξ,rowProduct C L d ξ ∂μ I)=∏ j : Slot I,(C.χ (Real.log (d j:ℝ)/L):ℂ) := by
  unfold rowProduct μ
  rw [integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact divisor_inversion C L (d j) (hd j)

/-- Exact finite signed divisor table: finite Fubini in both slot
coordinates and in an arbitrary literal positive divisor table.
The coefficient can be exactly the signed Möbius times CRT mass.
Terms with a divisor outside the original cutoff vanish only AFTER
this exact Fourier integral, as dictated by the actual χ. -/
theorem integral_divisor_table (C : Cutoff) (L : ℝ) (hL : 0<L) (Q : Finset (Digits I))
    (c : Digits I→ℂ) (hQ : ∀ d∈Q,∀ j,0<d j) :
    (∫ ξ, (∑ d∈Q,c d*rowProduct C L d ξ) ∂μ I) =
      ∑ d∈Q,c d*(∏ j : Slot I,(C.χ (Real.log (d j:ℝ)/L):ℂ)) := by
  classical
  rw [integral_finsetSum Q (fun d hd => (rowProduct_integrable C L d (hQ d hd)).const_mul (c d))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [integral_const_mul,rowProduct_integral C L hL d (hQ d hd)]

/-- The pointwise exact ABSOLUTE divisor-sum envelope factors the
common product of |φ|, with no imaginary-frequency dependence in
its remaining arithmetic coefficient. -/
theorem absolute_divisor_table (C : Cutoff) (L : ℝ) (Q : Finset (Digits I))
    (c : Digits I→ℂ) (hQ : ∀ d∈Q,∀ j,0<d j) (ξ : Slot I→ℝ) :
    (∑ d∈Q,‖c d*rowProduct C L d ξ‖)=
       (∏ j : Slot I,‖φ C (ξ j)‖) *
        ∑ d∈Q,‖c d‖*(∏ j : Slot I,(d j:ℝ)^(-(1/L))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [rowProduct,norm_mul,Complex.norm_prod]
  calc
    _ = ‖c d‖*(∏ j : Slot I,‖φ C (ξ j)‖*(d j:ℝ)^(-(1/L))) := by
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      exact spectral_norm C L (d j) (hQ d hd j) (ξ j)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      ring

/-- The source's original cutoff is reinserted only after inversion.
The input table can include arbitrarily large products of the primes
in the finite prime universe; none are dropped prematurely. -/
theorem restore_literal_cut (C : Cutoff) (R : ℝ) (hR : 1<R)
    (Q : Finset (Digits I)) (c : Digits I→ℂ) (hQ : ∀ d∈Q,∀ j,0<d j) :
    (∫ ξ, (∑ d∈Q,c d*rowProduct C (Real.log R) d ξ) ∂μ I) =
      ∑ d∈Q.filter (fun d => ∀ j,d j≤⌊R⌋₊),
        c d*(∏ j : Slot I,(C.χ (Real.log (d j:ℝ)/Real.log R):ℂ)) := by
  classical
  rw [integral_divisor_table C (Real.log R) (Real.log_pos hR) Q c hQ,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases H : ∀ j,d j≤⌊R⌋₊
  · rw [if_pos H]
  · rw [if_neg H]
    obtain ⟨j,hj⟩ := not_forall.mp H
    have hR₀ : 0≤R := le_trans zero_le_one hR.le
    have hgt : R<(d j:ℝ) := lt_of_not_ge
      (fun hz => hj ((Nat.le_floor_iff hR₀).2 hz))
    have hb : 1<Real.log (d j:ℝ)/Real.log R :=
      (lt_div_iff₀ (Real.log_pos hR)).2 (by
        rw [one_mul]
        exact Real.log_lt_log (zero_lt_one.trans hR) hgt)
    have hz : C.χ (Real.log (d j:ℝ)/Real.log R)=0 :=
      C.support _ (hb.trans_le (le_abs_self _))
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp only [hz,Complex.ofReal_zero]),mul_zero]

end ActualTZLiteralMellinTensor318
