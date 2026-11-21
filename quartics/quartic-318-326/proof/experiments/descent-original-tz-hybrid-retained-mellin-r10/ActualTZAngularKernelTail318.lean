module
public import ActualTZAngularKernelMain318
public import ActualTZAngularTensorTail318
public import ActualTZLowFrequencyPole318
public section
noncomputable section
namespace ActualTZAngularKernelTail318
open MeasureTheory Filter Set
open scoped BigOperators Topology
open ActualTZAngularKernelMain318 ActualTZAngularTensorTail318
open ActualTZLiteralMellinTensor318 ActualTZLiteralSchwartz318 ActualTZLowFrequencyPole318

variable {I : Type*} [Fintype I]

/-- The *absolute* actual signed main kernel outside the same
moving band tends to zero by Bochner dominated convergence.
There is no unnormalized/full-reference angular claim outside it. -/
theorem main_tail_tendsto (C : Cutoff) :
    Tendsto (fun L : ℝ=>∫ ξ in (fullBand I (band L))ᶜ,
      ‖mainDensity C ξ‖ ∂μ I) atTop (𝓝 0) := by
  classical
  let g (ξ : Slot I→ℝ) : ℝ := ‖mainDensity C ξ‖
  let S (L : ℝ) := (fullBand I (band L))ᶜ
  let F (L : ℝ) := (S L).indicator g
  have hg : Integrable g (μ I) := (main_integrable C).norm
  have hMeas (L : ℝ) : MeasurableSet (S L) := (fullBand_measurable (band L)).compl
  have hD : Tendsto (band : ℝ→ℝ) atTop atTop := _root_.tendsto_rpow_atTop (by norm_num)
  have hMe : ∀ᶠ L : ℝ in atTop,AEStronglyMeasurable (F L) (μ I) :=
    Eventually.of_forall (fun L => (hg.indicator (hMeas L)).aestronglyMeasurable)
  have hBound : ∀ᶠ L : ℝ in atTop,∀ᵐ ξ ∂μ I,‖F L ξ‖≤g ξ := by
    apply Eventually.of_forall
    intro L
    apply Eventually.of_forall
    intro ξ
    by_cases hx : ξ∈S L
    · rw [F,Set.indicator_of_mem hx,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    · rw [F,Set.indicator_of_notMem hx,norm_zero]
      exact norm_nonneg _
  have hLim : ∀ᵐ ξ ∂μ I,Tendsto (fun L : ℝ=>F L ξ) atTop (𝓝 ((fun _ : Slot I→ℝ=>(0:ℝ)) ξ)) := by
    apply Eventually.of_forall
    intro ξ
    let A := ∑ j : Slot I,‖ξ j‖
    obtain ⟨L₀,hL⟩ := tendsto_atTop_atTop.mp hD A
    have HQ : (fun L : ℝ=>F L ξ) =ᶠ[atTop] (fun _ : ℝ=>(0:ℝ)) := by
      refine eventually_atTop.mpr ⟨L₀,fun L h=>?_⟩
      have hInside : ξ∈fullBand I (band L) := by
        intro j
        have hh : ‖ξ j‖≤A :=
          Finset.single_le_sum (fun u _=>norm_nonneg (ξ u)) (Finset.mem_univ j)
        exact hh.trans (hL L h)
      have hOutside : ξ∉S L := fun h' => h' hInside
      exact indicator_of_notMem hOutside _
    exact tendsto_const_nhds.congr' HQ.symm
  have H := tendsto_integral_filter_of_dominated_convergence g hMe hBound hg hLim
  have he (L : ℝ) : (∫ ξ,F L ξ ∂μ I) = ∫ ξ in S L,g ξ ∂μ I :=
    integral_indicator (hMeas L)
  simp_rw [he,integral_zero] at H
  exact H

end ActualTZAngularKernelTail318
