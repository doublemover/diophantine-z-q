module
public import ActualTZLiteralSchwartz318
public section
noncomputable section
namespace ActualTZMellinFubini318
open MeasureTheory Set Filter
open scoped Topology
open ActualTZMellinKernel318 ActualTZLiteralSchwartz318

private abbrev μplus : Measure ℝ := volume.restrict (Set.Ioi 0)

@[expose] def row (C : Cutoff) (ξ u : ℝ) : ℂ :=
  ψ C ξ*Complex.exp (-mode ξ*(u:ℂ))

private theorem row_cont (C : Cutoff) : Continuous (fun p : ℝ×ℝ => row C p.1 p.2) := by
  have h : Continuous (ψ C) := ψ_continuous C
  unfold row mode
  fun_prop

private theorem row_norm (C : Cutoff) (ξ u : ℝ) : ‖row C ξ u‖=‖ψ C ξ‖*Real.exp (-u) := by
  unfold row
  rw [norm_mul,Complex.norm_exp]
  have he : ((-mode ξ)*(u:ℂ)).re=-u := by
    simp [Complex.mul_re,mode_re]
  rw [he]

private theorem exp_factor (u : ℝ) : Real.exp (-u)*Real.exp (-u)=Real.exp (-2*u) := by
  rw [←Real.exp_add]
  congr 1
  ring

private theorem damp : Integrable (fun u : ℝ => Real.exp (-2*u)) μplus :=
  integrableOn_exp_mul_Ioi (by norm_num : (-2:ℝ)<0) 0

private theorem row_pair_norm (C : Cutoff) (ξ η u : ℝ) :
    ‖row C ξ u*row C η u‖=‖ψ C ξ‖*Real.exp (-2*u)*‖ψ C η‖ := by
  rw [norm_mul,row_norm,row_norm,←exp_factor]
  ring

private theorem conditional_pair (C : Cutoff) (ξ : ℝ) :
    Integrable (Function.uncurry fun η u => row C ξ u*row C η u)
      ((volume : Measure ℝ).prod μplus) := by
  have hψ := (ψ_integrable C).norm
  have h : Integrable (fun p : ℝ×ℝ =>
      ‖ψ C p.1‖*Real.exp (-2*p.2)) ((volume : Measure ℝ).prod μplus) := hψ.mul_prod damp
  have hcont : Continuous (fun p : ℝ×ℝ => row C ξ p.2*row C p.1 p.2) := by
    have hr := row_cont C
    exact (hr.comp (continuous_const.prodMk continuous_snd)).mul hr
  apply (h.const_mul ‖ψ C ξ‖).mono' hcont.aestronglyMeasurable
  filter_upwards [] with p
  simp only [Function.uncurry,Pi.mul_apply,row_pair_norm]
  exact le_of_eq (by ring)

private theorem joint_triple (C : Cutoff) :
    Integrable (fun p : (ℝ×ℝ)×ℝ => row C p.1.1 p.1.2*row C p.2 p.1.2)
      (((volume : Measure ℝ).prod μplus).prod (volume : Measure ℝ)) := by
  have hψ := (ψ_integrable C).norm
  have h := (hψ.mul_prod damp).mul_prod hψ
  have hr := row_cont C
  have hcont :
      Continuous (fun p : (ℝ×ℝ)×ℝ => row C p.1.1 p.1.2*row C p.2 p.1.2) := by
    exact (hr.comp continuous_fst).mul (hr.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
  apply h.mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => le_of_eq (row_pair_norm C p.1.1 p.2 p.1.2))

private theorem laplace_step (C : Cutoff) (ξ η : ℝ) :
    φ C ξ*φ C η*kernel ξ η = ∫ u : ℝ in Set.Ioi 0,row C ξ u*row C η u := by
  rw [kernel_laplace]
  rw [←mul_assoc,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  unfold row ψ
  ring

/-- The complex two-frequency kernel is itself absolutely integrable
on the product measure, not merely evaluable as an iterated Bochner
integral. -/
theorem kernel_integrable (C : Cutoff) :
    Integrable (fun p : ℝ×ℝ => φ C p.1*φ C p.2*kernel p.1 p.2)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hm : Continuous mode := by unfold mode; fun_prop
  have hK : Continuous (fun p : ℝ×ℝ => kernel p.1 p.2) :=
    ((hm.comp continuous_fst).mul (hm.comp continuous_snd)).div
      ((hm.comp continuous_fst).add (hm.comp continuous_snd))
      (fun p => sum_ne_zero p.1 p.2)
  have hφ := φ_continuous C
  have hcont := ((hφ.comp continuous_fst).mul (hφ.comp continuous_snd)).mul hK
  have hψ := (ψ_integrable C).norm
  apply (hψ.mul_prod hψ).mono' hcont.aestronglyMeasurable
  filter_upwards [] with p
  have hd : 1≤‖mode p.1+mode p.2‖ := by
    have H := Complex.re_le_norm (mode p.1+mode p.2)
    rw [sum_re] at H
    linarith
  have he : φ C p.1*φ C p.2*kernel p.1 p.2 =
      (ψ C p.1*ψ C p.2)/(mode p.1+mode p.2) := by
    simp only [kernel,ψ,div_eq_mul_inv]
    ring
  rw [he,norm_div,norm_mul]
  calc
    _ ≤ (‖ψ C p.1‖*‖ψ C p.2‖)/1 :=
      div_le_div_of_nonneg_left (by positivity) zero_lt_one hd
    _ = _ := div_one _

/-- Proved with absolute Bochner integrability of the triple product,
not a formal exchange of iterated integrals. The real derivative is
squared, with the same signed transform in both slots. -/
theorem unnormalized_kernel (C : Cutoff) :
    (∫ ξ : ℝ,∫ η : ℝ,φ C ξ*φ C η*kernel ξ η) =
      ∫ u : ℝ in Set.Ioi 0,(deriv C.χ u:ℂ)^2 := by
  calc
    _ = ∫ ξ : ℝ,∫ η : ℝ,∫ u : ℝ in Set.Ioi 0,row C ξ u*row C η u := by
      simp only [laplace_step]
    _ = ∫ ξ : ℝ,∫ u : ℝ in Set.Ioi 0,∫ η : ℝ,row C ξ u*row C η u := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      exact integral_integral_swap (conditional_pair C ξ)
    _ = ∫ u : ℝ in Set.Ioi 0,∫ ξ : ℝ,∫ η : ℝ,row C ξ u*row C η u := by
      have h := (joint_triple C).integral_prod_left
      exact integral_integral_swap h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [integral_const_mul,integral_mul_const]
      have h : (∫ ξ : ℝ,row C ξ u)=-(deriv C.χ u:ℂ) := literal_derivative C u
      rw [h,pow_two]
      ring

private theorem deriv_zero_after (C : Cutoff) (u : ℝ) (hu : 1<u) : deriv C.χ u=0 := by
  have he : C.χ =ᶠ[𝓝 u] fun _ : ℝ => 0 := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact C.support v (lt_of_lt_of_le hv (le_abs_self _))
  rw [he.deriv_eq]
  simp

/-- This consumes exactly the preexisting real cutoff normalization
from PublishedCutoff. It does not assume the complex kernel integral. -/
theorem kernel_one (C : Cutoff)
    (hχ : (∫ u in (0:ℝ)..1,|deriv C.χ u|^2)=1) :
    (∫ ξ : ℝ,∫ η : ℝ,φ C ξ*φ C η*kernel ξ η)=1 := by
  rw [unnormalized_kernel]
  have hsub : Set.Ioc (0:ℝ) 1 ⊆ Set.Ioi 0 := fun u hu => hu.1
  have hcast : (∫ u : ℝ in Set.Ioi 0,(deriv C.χ u:ℂ)^2) =
      (∫ u : ℝ in Set.Ioc (0:ℝ) 1,(deriv C.χ u:ℂ)^2) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
    intro u hu
    have h₁ : 1<u := by
      by_contra h
      exact hu.2 ⟨hu.1,le_of_not_gt h⟩
    rw [deriv_zero_after C u h₁]
    simp
  rw [hcast]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] at hχ
  have he (u : ℝ) : (deriv C.χ u:ℂ)^2=((|deriv C.χ u|^2:ℝ):ℂ) := by
    rw [Complex.ofReal_pow, sq_abs]
  simp_rw [he]
  have h : (∫ u : ℝ in Set.Ioc (0:ℝ) 1,((|deriv C.χ u|^2:ℝ):ℂ)) =
      ((∫ u : ℝ in Set.Ioc (0:ℝ) 1,|deriv C.χ u|^2):ℂ) := by
    apply integral_ofReal
  rw [h,hχ]
  norm_cast

/-- Direct input shape of the original PublishedCutoff, without
importing its long PET/moment dependency graph. -/
theorem kernel_one_for (χ : ℝ→ℝ) (hSmooth : ContDiff ℝ ⊤ χ)
    (hSupport : ∀ u,1< |u|→χ u=0) (hEnergy : (∫ u in (0:ℝ)..1,|deriv χ u|^2)=1) :
    let C : Cutoff := ⟨χ,hSmooth.of_le le_top,hSupport⟩
    (∫ ξ : ℝ,∫ η : ℝ,φ C ξ*φ C η*kernel ξ η)=1 := by
  exact kernel_one ⟨χ,hSmooth.of_le le_top,hSupport⟩ hEnergy

end ActualTZMellinFubini318
