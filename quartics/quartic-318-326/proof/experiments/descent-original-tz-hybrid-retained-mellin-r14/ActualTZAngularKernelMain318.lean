module
public import ActualTZAngularPairs318
public import ActualTZMellinFubini318
public section
noncomputable section
namespace ActualTZAngularKernelMain318
open MeasureTheory
open scoped BigOperators
open ActualTZAngularPairs318 ActualTZLiteralMellinTensor318
open ActualTZMellinKernel318 ActualTZMellinFubini318 ActualTZLiteralSchwartz318

variable {I : Type*} [Fintype I]

@[expose] def single (C : Cutoff) (ξ : ℝ×ℝ) : ℂ :=
  φ C ξ.1*φ C ξ.2*kernel ξ.1 ξ.2

@[expose] def mainDensity (C : Cutoff) (ξ : Slot I→ℝ) : ℂ :=
  ∏ i : I,single C (ξ (i,true),ξ (i,false))

theorem mainDensity_product (C : Cutoff) (ξ : Slot I→ℝ) :
    mainDensity C ξ =
      (∏ j : Slot I,φ C (ξ j))*(∏ i : I,kernel (ξ (i,true)) (ξ (i,false))) := by
  simp only [mainDensity,single,Finset.prod_mul_distrib,Fintype.prod_prod_type,Fintype.prod_bool]

theorem main_integrable (C : Cutoff) : Integrable (mainDensity (I:=I) C) (μ I) := by
  have ht : Integrable (fun z : I→ℝ×ℝ=>∏ i : I,single C (z i))
      (Measure.pi fun _ : I=>(volume:Measure ℝ).prod volume) :=
    Integrable.fintype_prod (fun _ : I=>kernel_integrable C)
  have H := ((pairing_preserves I).integrable_comp_emb (pairing I).measurableEmbedding).2 ht
  simpa only [Function.comp_def,pairing_apply,mainDensity] using H

/-- The actual 2k-coordinate kernel integral equals one. Each
prior derivative-energy identity uses the same signed Fourier φ
twice, not an absolute square or a differently normalized measure. -/
theorem main_one (C : Cutoff) (hχ : (∫ u in (0:ℝ)..1,|deriv C.χ u|^2)=1) :
    (∫ ξ : Slot I→ℝ,mainDensity C ξ ∂μ I)=1 := by
  calc
    _ = ∫ z : I→ℝ×ℝ,(∏ i : I,single C (z i))
        ∂(Measure.pi fun _ : I=>(volume:Measure ℝ).prod volume) := by
      rw [←(pairing_preserves I).integral_comp']
      simp only [mainDensity,pairing_apply]
    _ = ∏ _i : I,∫ z : ℝ×ℝ,single C z ∂((volume:Measure ℝ).prod volume) :=
      integral_fintype_prod_eq_prod _
    _ = _ := by
      have h : (∫ z : ℝ×ℝ,single C z ∂((volume:Measure ℝ).prod volume))=1 := by
        rw [integral_prod _ (kernel_integrable C)]
        exact kernel_one C hχ
      simp only [h,Finset.prod_const_one]

end ActualTZAngularKernelMain318
