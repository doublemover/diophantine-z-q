module
public import TorusAddition318
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public section
noncomputable section
open Filter Set
open scoped Topology
namespace FiniteAnalyticCharts318
open PeriodEisenstein318 LatticeInvariants318
set_option maxHeartbeats 0

lemma analytic_inverse {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hd : deriv f z≠0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (f z) ∧ g (f z)=z ∧
      (fun w => g (f w)) =ᶠ[𝓝 z] id ∧ (fun w => f (g w)) =ᶠ[𝓝 (f z)] id := by
  let g := hf.hasStrictDerivAt.localInverse f (deriv f z) z hd
  have hl : (fun w => g (f w)) =ᶠ[𝓝 z] id := hf.hasStrictDerivAt.eventually_left_inverse hd
  refine ⟨g,hf.analyticAt_localInverse hd,hl.self_of_nhds,hl,?_⟩
  exact hf.hasStrictDerivAt.eventually_right_inverse hd

lemma xCoord_analytic (tau : UpperHalfPlane) (z : ℂ) (hz : z ∉ (periods tau).lattice) :
    AnalyticAt ℂ (xCoord tau) z := by
  have hp := (periods tau).analyticOnNhd_weierstrassP z hz
  unfold xCoord
  fun_prop

lemma yCoord_analytic (tau : UpperHalfPlane) (z : ℂ) (hz : z ∉ (periods tau).lattice) :
    AnalyticAt ℂ (yCoord tau) z := by
  have hp := (periods tau).analyticOnNhd_derivWeierstrassP z hz
  unfold yCoord
  fun_prop

lemma normalized_derivatives_nonzero (tau : UpperHalfPlane) (z : ℂ)
    (hz : z ∉ (periods tau).lattice) : deriv (xCoord tau) z≠0 ∨ deriv (yCoord tau) z≠0 := by
  have hp : (Real.pi : ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : 2*(Real.pi:ℂ)≠0 := mul_ne_zero (by norm_num) hp
  rcases WeierstrassImmersion318.pair_derivative_nonzero tau z hz with h | h
  · left
    unfold xCoord
    rw [deriv_div_const,(periods tau).deriv_weierstrassP]
    exact div_ne_zero h (pow_ne_zero 2 hk)
  · right
    unfold yCoord
    rw [deriv_div_const]
    exact div_ne_zero h (mul_ne_zero (by norm_num) (pow_ne_zero 3 hk))

/-- At every finite elliptic point the actual normalized x or y coordinate is a
holomorphic local coordinate, with an actual holomorphic inverse recovering the lattice argument. -/
theorem exists_finite_chart (tau : UpperHalfPlane) (z : ℂ)
    (hz : z ∉ (periods tau).lattice) :
    ∃ f g : ℂ → ℂ, (f=xCoord tau ∨ f=yCoord tau) ∧ AnalyticAt ℂ f z ∧
      AnalyticAt ℂ g (f z) ∧ g (f z)=z ∧
      (fun w => g (f w)) =ᶠ[𝓝 z] id ∧ (fun w => f (g w)) =ᶠ[𝓝 (f z)] id := by
  rcases normalized_derivatives_nonzero tau z hz with hx | hy
  · have hf := xCoord_analytic tau z hz
    obtain ⟨g,hg,hval,hl,hr⟩ := analytic_inverse hf hx
    exact ⟨xCoord tau,g,Or.inl rfl,hf,hg,hval,hl,hr⟩
  · have hf := yCoord_analytic tau z hz
    obtain ⟨g,hg,hval,hl,hr⟩ := analytic_inverse hf hy
    exact ⟨yCoord tau,g,Or.inr rfl,hf,hg,hval,hl,hr⟩

/-- Both actual affine coordinates are holomorphic functions of the selected local coordinate. -/
theorem finite_chart_graph (tau : UpperHalfPlane) (z : ℂ)
    (hz : z ∉ (periods tau).lattice) :
    ∃ f g : ℂ → ℂ, (f=xCoord tau ∨ f=yCoord tau) ∧
      AnalyticAt ℂ g (f z) ∧ g (f z)=z ∧
      AnalyticAt ℂ (fun t => xCoord tau (g t)) (f z) ∧
      AnalyticAt ℂ (fun t => yCoord tau (g t)) (f z) ∧
      (fun w => g (f w)) =ᶠ[𝓝 z] id ∧ (fun w => f (g w)) =ᶠ[𝓝 (f z)] id := by
  obtain ⟨f,g,hf,hfa,hg,hval,hl,hr⟩ := exists_finite_chart tau z hz
  refine ⟨f,g,hf,hg,hval,?_,?_,hl,hr⟩
  · have hx : AnalyticAt ℂ (xCoord tau) (g (f z)) := by rw [hval]; exact xCoord_analytic tau z hz
    exact hx.comp (f := g) hg
  · have hy : AnalyticAt ℂ (yCoord tau) (g (f z)) := by rw [hval]; exact yCoord_analytic tau z hz
    exact hy.comp (f := g) hg
end FiniteAnalyticCharts318
