module
public import Mathlib.NumberTheory.Modular
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic
public section
noncomputable section

open UpperHalfPlane MeasureTheory Set
open scoped ENNReal NNReal MeasureTheory

namespace SelectedStandardModularFiniteVolume318

private abbrev Hor := Icc (-(1:ℝ)/2) (1/2)
private abbrev Ver := Ioi ((1:ℝ)/2)
private abbrev Strip := Hor ×ˢ Ver
private def density (z : ℝ × ℝ) : ℝ≥0∞ := ENNReal.ofReal (z.2 ^ (-(2:ℝ)))

private theorem strip_integral_finite :
    (∫⁻ z in Strip, density z ∂(volume : Measure (ℝ × ℝ))) < ∞ := by
  let μ : Measure ℝ := volume.restrict Hor
  let ν : Measure ℝ := volume.restrict Ver
  letI : IsFiniteMeasure μ := ⟨by
    rw [show μ = (volume : Measure ℝ).restrict Hor from rfl,Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have hν : Integrable (fun y : ℝ => y ^ (-(2:ℝ))) ν :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-(2:ℝ)) < -1) (by norm_num : (0:ℝ) < 1/2)
  have hp := hν.comp_snd μ
  have hi : Integrable (fun z : ℝ×ℝ => z.2 ^ (-(2:ℝ)))
      ((volume : Measure (ℝ×ℝ)).restrict Strip) := by
    rw [Measure.volume_eq_prod,← Measure.prod_restrict]
    exact hp
  refine (lintegral_mono (fun z : ℝ × ℝ => Real.ofReal_le_enorm (z.2 ^ (-(2:ℝ))))).trans_lt ?_
  exact hi.hasFiniteIntegral

private theorem fd_in_strip : UpperHalfPlane.coe '' ModularGroup.fd ⊆
    Complex.measurableEquivRealProd ⁻¹' Strip := by
  rintro z ⟨τ,hτ,rfl⟩
  have h : |τ.re| ≤ (1:ℝ)/2 := hτ.2
  have h₃ := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
  refine ⟨?_,?_⟩
  · change -(1:ℝ) / 2 ≤ τ.re ∧ τ.re ≤ (1:ℝ) / 2
    simpa only [neg_div] using abs_le.mp h
  · change (1:ℝ)/2 < τ.im
    by_contra! hb
    have hn := mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ (1:ℝ)/2 + τ.im by positivity)
    nlinarith

private theorem density_eq (z : ℂ) (hz : z ∈ Complex.measurableEquivRealProd ⁻¹' Strip) :
    (↑((1 / ‖z.im‖₊)^2 : ℝ≥0) : ℝ≥0∞) = density (Complex.measurableEquivRealProd z) := by
  have hy : 0 ≤ z.im := le_trans (by norm_num : (0:ℝ) ≤ 1/2) hz.2.le
  change (↑((1 / ‖z.im‖₊)^2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (z.im ^ (-(2:ℝ)))
  rw [Real.rpow_neg hy,Real.rpow_two,← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp only [one_div,inv_pow,NNReal.coe_inv,NNReal.coe_pow,coe_nnnorm,Real.norm_of_nonneg hy]

/-- Finite hyperbolic area of the actual closed SL₂(ℤ) standard
domain. The upper tail is not treated as compact: it is compared
with the real product strip and the integrable y⁻² density. -/
theorem standard_fd_finite : (volume : Measure UpperHalfPlane) ModularGroup.fd < ∞ := by
  let E := Complex.measurableEquivRealProd
  let V : Set ℂ := E ⁻¹' Strip
  have hm : MeasurableSet V := E.measurable (measurableSet_Icc.prod measurableSet_Ioi)
  have hread :
      (∫⁻ z in V, (↑((1/‖z.im‖₊)^2 : ℝ≥0) : ℝ≥0∞)) =
        ∫⁻ z in V, density (E z) :=
    setLIntegral_congr_fun hm density_eq
  have hpres := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    E.measurableEmbedding density Strip
  rw [UpperHalfPlane.volume_eq_lintegral]
  calc
    _ ≤ ∫⁻ z in V, (↑((1/‖z.im‖₊)^2 : ℝ≥0) : ℝ≥0∞) := lintegral_mono_set fd_in_strip
    _ = ∫⁻ z in V, density (E z) := hread
    _ = ∫⁻ z in Strip, density z := hpres
    _ < ∞ := strip_integral_finite

end SelectedStandardModularFiniteVolume318

#print axioms SelectedStandardModularFiniteVolume318.standard_fd_finite
