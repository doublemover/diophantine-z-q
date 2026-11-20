module
public import SelectedJOneCover318
public import SelectedWeightTwoPetersson318
public import SelectedGammaOneQuotientArea318
public import HolomorphicEnergy318
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Complex.OpenMapping
public section
noncomputable section
open MeasureTheory Set Metric Function UpperHalfPlane
open GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318 QuotientJ318
open SelectedWeightTwoPetersson318 SelectedGammaOneQuotientArea318
open scoped ENNReal NNReal

namespace SelectedJOneMeasuredEnergy318

private theorem cross_measurable {N : ℕ} (a b : Form N) : Measurable (cross a b) := by
  apply measurable_from_quotient.mpr
  change Measurable (UpperHalfPlane.petersson 2 a b)
  exact (UpperHalfPlane.petersson_continuous 2 a.holo'.continuous b.holo'.continuous).measurable

private theorem period_mass {N : ℕ} (a : Form N) (B : Set UpperHalfPlane)
    (hB : MeasurableSet B) :
    (∫⁻ τ in B, ENNReal.ofReal ((cross a a (quotientMap N τ)).re)) =
      ∫⁻ z in UpperHalfPlane.coe '' B, ENNReal.ofReal (‖a (UpperHalfPlane.ofComplex z)‖^2) := by
  let ρ : UpperHalfPlane → ℝ≥0∞ := fun τ => ENNReal.ofReal (τ.im^2)⁻¹
  have hρ : Measurable ρ := by
    exact ENNReal.measurable_ofReal.comp (show Measurable (fun τ : UpperHalfPlane => (τ.im^2)⁻¹) by fun_prop)
  let g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖a (UpperHalfPlane.ofComplex z)‖^2)
  have hvol : (volume : Measure UpperHalfPlane) =
      (volume.comap UpperHalfPlane.coe).withDensity ρ := by
    rw [UpperHalfPlane.volume_def]
    congr 1
    funext τ
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [ρ,one_div,inv_pow]
  have hπ : Measurable (quotientMap N) :=
    measurable_quotient_mk' (s := MulAction.orbitRel (image N) UpperHalfPlane)
  have hQ := ENNReal.measurable_ofReal.comp (Complex.continuous_re.measurable.comp
    ((cross_measurable a a).comp hπ))
  rw [hvol,setLIntegral_withDensity_eq_setLIntegral_mul _ hρ hQ hB]
  have hmp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨measurable_coe,by rw [measurableEmbedding_coe.map_comap]⟩
  have hp := hmp.setLIntegral_comp_emb measurableEmbedding_coe g B
  rw [Measure.restrict_restrict_of_subset (image_subset_range _ _)] at hp
  refine (lintegral_congr ?_).trans hp
  intro τ
  change ENNReal.ofReal (τ.im^2)⁻¹ * ENNReal.ofReal ((cross a a (quotientMap N τ)).re) =
    ENNReal.ofReal (‖a (UpperHalfPlane.ofComplex (τ : ℂ))‖^2)
  rw [← ENNReal.ofReal_mul (show 0 ≤ (τ.im^2)⁻¹ by positivity),
    mul_comm,← div_eq_mul_inv,UpperHalfPlane.ofComplex_apply,period_energy]

/-- Unit energy on an actual injective open period sheet now follows from
the same orthonormal complex Gram matrix over the canonical quotient
measure. No local-chart mass, global unit-vector energy, or arbitrary
replacement measure is an input. -/
theorem period_unit {N g : ℕ} (hN : 5 ≤ N) (B : Set UpperHalfPlane)
    (hB : IsOpen B) (hBI : InjOn (quotientMap N) B)
    (b : Fin g → Form N)
    (hI : ∀ i j, Integrable (cross (b i) (b j)) (area N hN))
    (hG : ∀ i j, (∫ q, cross (b i) (b j) q ∂(area N hN)) = if i = j then 1 else 0)
    (x : EuclideanSpace ℂ (Fin g)) (hx : ‖x‖ = 1) :
    IntegrableOn (fun z => ‖combination b x (UpperHalfPlane.ofComplex z)‖^2)
       (UpperHalfPlane.coe '' B) ∧
    (∫ z in UpperHalfPlane.coe '' B, ‖combination b x (UpperHalfPlane.ofComplex z)‖^2) ≤ 1 := by
  let μ := area N hN
  let a := combination b x
  let f : ℂ → ℝ := fun w => ‖a (UpperHalfPlane.ofComplex w)‖^2
  let R (q : Base (image N)) : ℝ := (cross a a q).re
  let T := UpperHalfPlane.coe '' B
  have hi := (gram_energy μ b hI hG x).1
  have hir : Integrable R μ := (RCLike.reCLM : ℂ →L[ℝ] ℝ).integrable_comp hi
  have he : (∫ q, R q ∂μ) = 1 := by
    have h := integral_re hi
    change (∫ q, R q ∂μ) = (∫ q, cross a a q ∂μ).re at h
    rw [h,unit_energy μ b hI hG x hx] <;> norm_num
  have hr (q : Base (image N)) : 0 ≤ R q := by
    obtain ⟨τ,rfl⟩ := GammaOneAtlas318.quotient_surjective N q
    have h := (div_eq_iff (pow_ne_zero 2 τ.im_ne_zero)).mp (period_energy a τ)
    change R (quotientMap N τ) = ‖a τ‖^2 * τ.im^2 at h
    rw [h]
    positivity
  have hrm : Measurable (fun q => ENNReal.ofReal (R q)) :=
    ENNReal.measurable_ofReal.comp (Complex.continuous_re.measurable.comp
      (cross_measurable a a))
  have hπ : Measurable (quotientMap N) :=
    measurable_quotient_mk' (s := MulAction.orbitRel (image N) UpperHalfPlane)
  have hmass : (∫⁻ z in T, ENNReal.ofReal (f z)) ≤ 1 := by
    rw [← period_mass a B hB.measurableSet,← lintegral_map hrm hπ]
    calc
      _ ≤ ∫⁻ q, ENNReal.ofReal (R q) ∂μ :=
        lintegral_mono' (sheet_area_le N hN B hB hBI) le_rfl
      _ = 1 := by rw [← ofReal_integral_eq_lintegral_ofReal hir
        (Filter.Eventually.of_forall hr),he,ENNReal.ofReal_one]
  have hTa : T ⊆ UpperHalfPlane.upperHalfPlaneSet := by
    rintro z ⟨τ,_,rfl⟩
    exact τ.im_pos
  have hc : ContinuousOn f T := by
    have ha := (UpperHalfPlane.mdifferentiable_iff.mp a.holo').continuousOn
    exact ((ha.mono hTa).norm).pow 2
  have hn : 0 ≤ᵐ[volume.restrict T] f := Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hm : MeasurableSet T :=
    UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hB.measurableSet
  have hf : IntegrableOn f T :=
    ⟨hc.aestronglyMeasurable hm,(hasFiniteIntegral_iff_ofReal hn).mpr
      (hmass.trans_lt (by simp))⟩
  refine ⟨hf,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hf hn] at hmass
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ)≤1)).mp (by simpa using hmass)

private abbrev Disk := ↥(ball (0 : ℂ) 1)

/-- All Euclidean unit combinations on the literal open inverse disk
through this particular chosen j=1 quotient point. The *same* period
section works for all x and all entries of the chosen cusp-form basis.
No local energy or measure identity is supplied. The remaining geometric
input is that the actual stable Jacobian Hodge frame is this basis and has
the displayed Gram matrix on this canonical quotient measure. -/
theorem literal_inverse_disk {N g : ℕ} (hN : 5 ≤ N)
    (q : Base (image N)) (hq : jMap N q = 1)
    (b : Fin g → Form N)
    (hI : ∀ i j, Integrable (cross (b i) (b j)) (area N hN))
    (hG : ∀ i j, (∫ z, cross (b i) (b j) z ∂(area N hN)) = if i = j then 1 else 0) :
    ∃ T : C(↥(ball (0 : ℂ) 1), UpperHalfPlane), ∃ F : ℂ → ℂ,
      quotientMap N (T ⟨0, mem_ball_self (by norm_num)⟩) = q ∧
      (∀ z, F (z : ℂ) = (T z : ℂ)) ∧
      (∀ z, ActualQJ318.jInvariant (T z) = 1+(z : ℂ)) ∧
      ∀ x : EuclideanSpace ℂ (Fin g), ‖x‖ = 1 →
      let a := fun z => combination b x (UpperHalfPlane.ofComplex (F z)) * deriv F z
      DifferentiableOn ℂ a (ball 0 1) ∧
      IntegrableOn (fun z => ‖a z‖^2) (ball 0 1) ∧
      (∫ z in ball (0 : ℂ) 1, ‖a z‖^2) ≤ 1 := by
  obtain ⟨T,F,hcenter,hFT,hj,hF,hTI⟩ :=
    SelectedJOneCover318.holomorphic_disk_section N hN q hq
  let D := ball (0 : ℂ) 1
  let B := range T
  have hFD : F '' D = UpperHalfPlane.coe '' B := by
    ext w
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨T ⟨z,hz⟩, mem_range_self _, (hFT ⟨z,hz⟩).symm⟩
    · rintro ⟨τ,⟨z,rfl⟩,rfl⟩
      exact ⟨z,z.property,hFT z⟩
  have hBI : InjOn (quotientMap N) B := by
    rintro _ ⟨z,rfl⟩ _ ⟨w,rfl⟩ hzw
    exact congrArg T (hTI (mem_univ z) (mem_univ w) hzw)
  have hFI : InjOn F D := by
    intro z hz w hw he
    have hT : T ⟨z,hz⟩ = T ⟨w,hw⟩ := UpperHalfPlane.coe_injective
      ((hFT ⟨z,hz⟩).symm.trans (he.trans (hFT ⟨w,hw⟩)))
    exact congrArg Subtype.val (hTI (mem_univ _) (mem_univ _)
      (congrArg (quotientMap N) hT))
  have hDo : IsOpen (F '' D) := by
    rcases hF.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with hc | ho
    · obtain ⟨c,hc⟩ := hc
      have h0 : (0:ℂ) ∈ D := mem_ball_self (by norm_num)
      have hhalf : ((1/2:ℝ) : ℂ) ∈ D := by
        norm_num [D,mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
      have hf0 := hc (0:ℂ) h0
      have hf1 := hc ((1/2:ℝ) : ℂ) hhalf
      have hfneq := hFI h0 hhalf (hf0.trans hf1.symm)
      norm_num at hfneq
    · exact ho _ subset_rfl isOpen_ball
  have hB : IsOpen B := by
    rw [hFD] at hDo
    have h := UpperHalfPlane.continuous_coe.isOpen_preimage _ hDo
    rwa [preimage_image_eq _ UpperHalfPlane.coe_injective] at h
  refine ⟨T,F,hcenter,hFT,hj,?_⟩
  intro x hx
  let f : ℂ → ℂ := fun w => combination b x (UpperHalfPlane.ofComplex w)
  have ha : DifferentiableOn ℂ f (UpperHalfPlane.upperHalfPlaneSet) :=
    UpperHalfPlane.mdifferentiable_iff.mp (combination b x).holo'
  have hFDsub : F '' D ⊆ UpperHalfPlane.upperHalfPlaneSet := by
    rw [hFD]
    rintro _ ⟨τ,_,rfl⟩
    exact τ.im_pos
  have hh : DifferentiableOn ℂ F D := hF.differentiableOn
  have he := period_unit hN B hB hBI b hI hG x hx
  change IntegrableOn (fun z => ‖f z‖^2) (UpperHalfPlane.coe '' B) ∧
    (∫ z in UpperHalfPlane.coe '' B, ‖f z‖^2) ≤ 1 at he
  rw [← hFD] at he
  have hlocal := HolomorphicEnergy318.pullback_energy_one F f 0 1 (F '' D) hh hFI
    subset_rfl he.1 he.2
  refine ⟨(ha.comp hh ?_).mul (hh.deriv isOpen_ball),hlocal⟩
  intro z hz
  exact hFDsub ⟨z,hz,rfl⟩

end SelectedJOneMeasuredEnergy318
#print axioms SelectedJOneMeasuredEnergy318.period_unit
#print axioms SelectedJOneMeasuredEnergy318.literal_inverse_disk
