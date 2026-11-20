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

theorem actualKernel_integrable (κ τ X : ℝ) (i : Fin 4) (hτ : 0<τ) :
    Integrable (kernel κ τ X i) measure3 := by
  let K₄ : Set ℝ := Set.Icc (-4) 4
  let KV : Set ℝ := Set.Icc (-(2*τ)) (2*τ)
  let K : Set FreePoint := KV ×ˢ (K₄ ×ˢ K₄)
  have hk₄ : IsCompact K₄ := isCompact_Icc
  have hkV : IsCompact KV := isCompact_Icc
  have hk : IsCompact K := hkV.prod (hk₄.prod hk₄)
  have hs : Function.support (kernel κ τ X i) ⊆ K := by
    intro p hp
    have hn : sectionWeight κ τ i X p.2.2 p.2.1 p.1≠0 := by
      intro h
      exact hp (by simp [kernel,W,h])
    have h := section_nonzero_box κ τ i X p.2.2 p.2.1 p.1 hτ hn
    exact ⟨abs_le.mp h.2.2.2.2.le,abs_le.mp h.2.2.2.1,abs_le.mp h.2.2.1⟩
  have hcs : HasCompactSupport (kernel κ τ X i) := by
    change IsCompact (closure (Function.support (kernel κ τ X i)))
    exact hk.of_isClosed_subset isClosed_closure (closure_minimal hs hk.isClosed)
  have hperm : Continuous (fun p : FreePoint => (p.2.2,p.2.1,p.1)) :=
    continuous_snd.snd.prodMk (continuous_snd.fst.prodMk continuous_fst)
  have hc : Continuous (kernel κ τ X i) := (affine_smooth κ τ i X).continuous.comp hperm
  unfold measure3
  exact hc.integrable_of_hasCompactSupport hcs

end ActualPureChartKernel318
