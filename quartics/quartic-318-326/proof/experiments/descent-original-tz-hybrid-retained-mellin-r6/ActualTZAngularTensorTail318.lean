module
public import ActualTZLiteralMellinTensor318
public section
noncomputable section
namespace ActualTZAngularTensorTail318
open MeasureTheory Set
open scoped BigOperators Topology
open ActualTZLiteralSchwartz318
open ActualTZLiteralMellinTensor318

variable {I : Type*} [Fintype I]

@[expose] def density (C : Cutoff) (ξ : Slot I→ℝ) : ℝ :=
  ∏ j : Slot I,‖φ C (ξ j)‖

theorem density_nonneg (C : Cutoff) (ξ : Slot I→ℝ) : 0≤density C ξ :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

theorem density_integrable (C : Cutoff) : Integrable (density (I:=I) C) (μ I) :=
  Integrable.fintype_prod (fun _ : Slot I => (φ_integrable C).norm)

@[expose] def fullBand (I : Type*) (H : ℝ) : Set (Slot I→ℝ) :=
  {ξ | ∀ j,‖ξ j‖≤H}

theorem fullBand_measurable (H : ℝ) : MeasurableSet (fullBand I H) := by
  have Hs : fullBand I H=⋂ j : Slot I,{ξ : Slot I→ℝ | ‖ξ j‖≤H} := by
    ext ξ
    simp only [fullBand,Set.mem_setOf_eq,Set.mem_iInter]
  rw [Hs]
  exact MeasurableSet.iInter fun j =>
    measurableSet_le ((continuous_apply j).norm.measurable) measurable_const

def moments (C : Cutoff) (d : ℕ) (ξ : Slot I→ℝ) : ℝ :=
  ∑ j : Slot I,‖ξ j‖^d*density C ξ

private theorem single_moment (C : Cutoff) (d : ℕ) (j : Slot I) :
    Integrable (fun ξ : Slot I→ℝ=>‖ξ j‖^d*density C ξ) (μ I) := by
  classical
  let v (i : Slot I) (x : ℝ) := if i=j then ‖x‖^d*‖φ C x‖ else ‖φ C x‖
  have hv (i : Slot I) : Integrable (v i) := by
    by_cases h : i=j
    · simpa only [v,if_pos h] using φ_moments C d
    · simpa only [v,if_neg h] using (φ_integrable C).norm
  have he (ξ : Slot I→ℝ) :
      (∏ i : Slot I,v i (ξ i))=‖ξ j‖^d*density C ξ := by
    have H (i : Slot I) : v i (ξ i)=(if i=j then ‖ξ i‖^d else 1)*‖φ C (ξ i)‖ := by
      by_cases h : i=j <;> simp [v,h]
    simp only [H,Finset.prod_mul_distrib,density]
    congr 1
    rw [Finset.prod_eq_single j]
    · simp
    · intro i _ hi; exact if_neg hi
    · simp
  convert Integrable.fintype_prod hv using 1
  funext ξ
  exact (he ξ).symm

theorem moments_integrable (C : Cutoff) (d : ℕ) :
    Integrable (moments (I:=I) C d) (μ I) := by
  unfold moments
  exact integrable_finsetSum _ (fun j _=>single_moment C d j)

theorem moments_nonneg (C : Cutoff) (d : ℕ) (ξ : Slot I→ℝ) : 0≤moments C d ξ := by
  unfold moments
  exact Finset.sum_nonneg fun _ _=>mul_nonneg (by positivity) (density_nonneg C ξ)

private theorem point_outside (C : Cutoff) (d : ℕ) (H : ℝ) (hH : 0<H)
    (ξ : Slot I→ℝ) (hξ : ξ∈(fullBand I H)ᶜ) :
    density C ξ≤(H^d)⁻¹*moments C d ξ := by
  classical
  have hNot : ¬∀ j,‖ξ j‖≤H := hξ
  obtain ⟨j,hj⟩ := not_forall.mp hNot
  have hp : H^d≤‖ξ j‖^d := pow_le_pow_left₀ hH.le (le_of_not_ge hj) d
  have hterm : ‖ξ j‖^d*density C ξ≤moments C d ξ := by
    unfold moments
    exact Finset.single_le_sum (fun i _=>mul_nonneg (by positivity) (density_nonneg C ξ))
      (Finset.mem_univ j)
  rw [←div_eq_inv_mul]
  apply (le_div_iff₀ (pow_pos hH d)).2
  calc
    _ = H^d*density C ξ := mul_comm _ _
    _ ≤ _ := (mul_le_mul_of_nonneg_right hp (density_nonneg C ξ)).trans hterm

/-- Exact all-slot high-frequency complement, with no change of
Haar/2π convention. The fixed constant is the integral of the sum
of actual d-th moment densities over the 2k original slots. -/
theorem outside_bound (C : Cutoff) (d : ℕ) (H : ℝ) (hH : 0<H) :
    (∫ ξ in (fullBand I H)ᶜ,density C ξ ∂μ I) ≤
      (H^d)⁻¹*(∫ ξ,moments C d ξ ∂μ I) := by
  let D := (fullBand I H)ᶜ
  let g (ξ : Slot I→ℝ) := (H^d)⁻¹*moments C d ξ
  have hg : Integrable g (μ I) := (moments_integrable C d).const_mul _
  calc
    _ ≤ ∫ ξ in D,g ξ ∂μ I := by
      exact setIntegral_mono_on (density_integrable C).integrableOn hg.integrableOn
        (fullBand_measurable (I:=I) H).compl (point_outside C d H hH)
    _ ≤ ∫ ξ,g ξ ∂μ I := setIntegral_le_integral hg
      (Filter.Eventually.of_forall (fun ξ=>mul_nonneg (by positivity) (moments_nonneg C d ξ)))
    _ = _ := by simp only [g,integral_const_mul]

/-- A positive pointwise weighted majorant gives a signed integral
bound on the high-frequency complement, not merely a norm-sum
comparison at fixed frequency. -/
theorem use_outside_bound (C : Cutoff) (d : ℕ) (H : ℝ) (hH : 0<H)
    (f : (Slot I→ℝ)→ℂ) (hf : Integrable f (μ I)) (A : ℝ) (hA : 0≤A)
    (hDom : ∀ ξ,‖f ξ‖≤A*density C ξ) :
    ‖∫ ξ in (fullBand I H)ᶜ,f ξ ∂μ I‖ ≤
      A*((H^d)⁻¹*(∫ ξ,moments C d ξ ∂μ I)) := by
  calc
    _ ≤ ∫ ξ in (fullBand I H)ᶜ,‖f ξ‖ ∂μ I := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ in (fullBand I H)ᶜ,A*density C ξ ∂μ I := by
      exact setIntegral_mono_on hf.norm.integrableOn ((density_integrable C).const_mul A).integrableOn
        (fullBand_measurable (I:=I) H).compl (fun ξ _=>hDom ξ)
    _ ≤ _ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (outside_bound C d H hH) hA

end ActualTZAngularTensorTail318
