module
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public section
noncomputable section
open Filter
open scoped Topology ContDiff
namespace AnalyticImplicitGraph318
set_option maxHeartbeats 0

lemma partial_invertible {f : ℂ × ℂ → ℂ} {p : ℂ × ℂ} {d : ℂ}
    (hf : AnalyticAt ℂ f p)
    (hd : HasDerivAt (fun y : ℂ => f (p.1,y)) d p.2) (hd0 : d≠0) :
    (fderiv ℂ f p ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  have hm := hasFDerivAt_prodMk_right (𝕜:=ℂ) p.1 p.2
  have hc := hf.differentiableAt.hasFDerivAt.comp p.2 hm
  have he := hc.unique (hd.hasFDerivAt_equiv hd0)
  exact ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d hd0),he.symm⟩

/-- The actual complex implicit function, with its value, holomorphy, equation,
and local uniqueness. The invertible partial is derived from a scalar derivative. -/
theorem exists_graph {f : ℂ × ℂ → ℂ} {p : ℂ × ℂ} {d : ℂ}
    (hf : AnalyticAt ℂ f p)
    (hd : HasDerivAt (fun y : ℂ => f (p.1,y)) d p.2) (hd0 : d≠0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p.1 ∧ g p.1=p.2 ∧
      (∀ᶠ z in 𝓝 p.1, f (z,g z)=f p) ∧
      (∀ᶠ v in 𝓝 p, f v=f p ↔ g v.1=v.2) := by
  have hc : ContDiffAt ℂ ω f p := hf.contDiffAt
  have hn : (ω : ℕ∞ω)≠0 := by decide
  have hi := partial_invertible hf hd hd0
  exact ⟨hc.implicitFunction hn hi,(hc.contDiffAt_implicitFunction hn hi).analyticAt,
    hc.implicitFunction_apply_self hn hi,hc.eventually_apply_implicitFunction hn hi,
    hc.eventually_apply_eq_iff_implicitFunction hn hi⟩

end AnalyticImplicitGraph318
