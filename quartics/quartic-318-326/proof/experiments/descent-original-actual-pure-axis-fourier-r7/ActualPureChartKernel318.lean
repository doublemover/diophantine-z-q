module
public import AffineThreePoissonRows318
public import ActualTubeChartSupport318
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public section
noncomputable section
namespace ActualPureChartKernel318
open MeasureTheory
open AffineThreePoissonRows318 ActualTubeAnnulusChart318 ActualTubeChartSupport318

/-- Canonical analytic alias of the exact Poisson-input weight; no
prime, congruence sheet or Y/Z Jet import is needed to state it. -/
@[expose] def W (κ τ : ℝ) (i : Fin 4) (X : ℝ) : Cube :=
  fun Z T V => (sectionWeight κ τ i X Z T V : ℂ)

abbrev FreePoint := ℝ × (ℝ × ℝ)

/-- Weight on precisely the product measure order (V,(T,Z)). -/
@[expose] def kernel (κ τ X : ℝ) (i : Fin 4) (p : FreePoint) : ℂ :=
  W κ τ i X p.2.2 p.2.1 p.1

def measure3 : Measure FreePoint :=
  (volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)

private def kernelBox (τ : ℝ) : Set FreePoint :=
  Set.Icc (-(2*τ)) (2*τ) ×ˢ (Set.Icc (-4) 4 ×ˢ Set.Icc (-4) 4)

private theorem kernelBox_compact (τ : ℝ) : IsCompact (kernelBox τ) := by
  have h₄ : IsCompact (Set.Icc (-4:ℝ) 4) := isCompact_Icc
  have hV : IsCompact (Set.Icc (-(2*τ)) (2*τ)) := isCompact_Icc
  exact hV.prod (h₄.prod h₄)

private theorem kernel_support_subset (κ τ X : ℝ) (i : Fin 4) (hτ : 0<τ) :
    Function.support (kernel κ τ X i) ⊆ kernelBox τ := by
  intro p hp
  have hn : sectionWeight κ τ i X p.2.2 p.2.1 p.1 ≠ 0 := by
    intro h
    apply hp
    change (sectionWeight κ τ i X p.2.2 p.2.1 p.1 : ℂ) = 0
    rw [h,Complex.ofReal_zero]
  obtain ⟨_,_,hZ,hT,hV⟩ := section_nonzero_box κ τ i X p.2.2 p.2.1 p.1 hτ hn
  change p.1 ∈ Set.Icc (-(2*τ)) (2*τ) ∧
    p.2.1 ∈ Set.Icc (-4:ℝ) 4 ∧ p.2.2 ∈ Set.Icc (-4:ℝ) 4
  exact ⟨abs_le.mp hV.le,abs_le.mp hT,abs_le.mp hZ⟩

private theorem kernel_compact_support (κ τ X : ℝ) (i : Fin 4) (hτ : 0<τ) :
    HasCompactSupport (kernel κ τ X i) := by
  have hk := kernelBox_compact τ
  have hs := kernel_support_subset κ τ X i hτ
  change IsCompact (closure (Function.support (kernel κ τ X i)))
  exact hk.of_isClosed_subset isClosed_closure (closure_minimal hs hk.isClosed)

/-- Reverse the three coordinates while the continuous callback is abstract.
This keeps continuity composition independent of the chart-weight definition. -/
private theorem continuous_reverseFree (φ : FreePoint → ℂ) (hφ : Continuous φ) :
    Continuous (fun p : FreePoint => φ (p.2.2,p.2.1,p.1)) := by
  let ρ : FreePoint → FreePoint := fun p => (p.2.2,p.2.1,p.1)
  have hpV : Continuous (fun p : FreePoint => p.1) := continuous_fst
  have hpT : Continuous (fun p : FreePoint => p.2.1) := continuous_snd.fst
  have hpZ : Continuous (fun p : FreePoint => p.2.2) := continuous_snd.snd
  have hρ : Continuous ρ := hpZ.prodMk (hpT.prodMk hpV)
  change Continuous (φ ∘ ρ)
  exact Continuous.comp (f := ρ) (g := φ) hφ hρ

set_option diagnostics true in
private theorem kernel_continuous (κ τ X : ℝ) (i : Fin 4) :
    Continuous (kernel κ τ X i) := by
  let φ : FreePoint → ℂ := fun p => (sectionWeight κ τ i X p.1 p.2.1 p.2.2 : ℂ)
  have hφ : Continuous φ := (affine_smooth κ τ i X).continuous
  change Continuous (fun p : FreePoint => φ (p.2.2,p.2.1,p.1))
  exact continuous_reverseFree φ hφ

private theorem measure3_finite_compacts : IsFiniteMeasureOnCompacts measure3 := by
  let μ : Measure ℝ := volume
  haveI : IsFiniteMeasureOnCompacts μ :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
  let ν : Measure (ℝ × ℝ) := μ.prod μ
  haveI : IsFiniteMeasureOnCompacts ν := Measure.prod.instIsFiniteMeasureOnCompacts μ μ
  change IsFiniteMeasureOnCompacts (μ.prod ν)
  exact Measure.prod.instIsFiniteMeasureOnCompacts μ ν

theorem actualKernel_integrable (κ τ X : ℝ) (i : Fin 4) (hτ : 0<τ) :
    Integrable (kernel κ τ X i) measure3 := by
  letI : IsFiniteMeasureOnCompacts measure3 := measure3_finite_compacts
  exact (kernel_continuous κ τ X i).integrable_of_hasCompactSupport
    (μ := measure3) (kernel_compact_support κ τ X i hτ)

end ActualPureChartKernel318
