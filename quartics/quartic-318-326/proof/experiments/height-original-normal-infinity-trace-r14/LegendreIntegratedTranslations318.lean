module
public import LegendreIntegratedCoordinates318
public import Mathlib.Analysis.Calculus.MeanValue
public section
noncomputable section
namespace LegendreIntegratedTranslations318
open Set Filter Metric
open scoped Topology
open LegendreCompletedComplexAtlas318 LegendreGlobalHolomorphicDifferential318
open LegendreDifferentialChartTransitions318 LegendreIntegratedCoordinates318

/-- Equal derivatives on a genuine neighborhood make primitive germs
differ by their exact center constant. No global simply-connectedness is
assumed or inferred from local integration. -/
lemma primitive_difference_constant (f g a : ℂ→ℂ) (z : ℂ)
    (hd : ∀ᶠ w in 𝓝 z,HasDerivAt f (a w) w ∧ HasDerivAt g (a w) w) :
    ∀ᶠ w in 𝓝 z,f w-g w=f z-g z := by
  obtain ⟨r,hr,hs⟩:=Metric.eventually_nhds_iff.mp hd
  have hdiff : DifferentiableOn ℂ (fun w=>f w-g w) (ball z r) :=
    fun w hw=>((hs hw).1.sub (hs hw).2).differentiableAt.differentiableWithinAt
  have hzero : (ball z r).EqOn (deriv (fun w=>f w-g w)) 0 := by
    intro w hw
    simpa only [sub_self] using ((hs hw).1.sub (hs hw).2).deriv
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
  exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z r).isPreconnected
    hdiff hzero hw (mem_ball_self hr)

variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]
/-- On each actual chart overlap, integrated coordinates differ by a
translation, with the constant computed at the actual same curve point.
This uses the already proved global differential cocycle, not an assumed
translation atlas or period-lattice identification. -/
theorem actual_overlap_translation (i j : ChartIndex l) (z : ℂ)
    (hz : z∈(Transition l i j).source) (f g : ℂ→ℂ)
    (hf : ∀ᶠ w in 𝓝 z,HasDerivAt f ((invariantDifferential l).coefficient i w) w)
    (hg : ∀ᶠ w in 𝓝 (Transition l i j z),
      HasDerivAt g ((invariantDifferential l).coefficient j w) w) :
    ∀ᶠ w in 𝓝 z,f w-g (Transition l i j w)=f z-g (Transition l i j z) := by
  have ht := (analytic_transition l i j z hz).continuousAt
  apply primitive_difference_constant f (fun w=>g (Transition l i j w))
    ((invariantDifferential l).coefficient i) z
  filter_upwards [hf,ht.tendsto.eventually hg,
    (Transition l i j).open_source.mem_nhds hz] with w hfw hgw hw
  refine ⟨hfw,?_⟩
  have htw := (analytic_transition l i j w hw).differentiableAt.hasDerivAt
  have hc := hgw.comp w htw
  rw [←(invariantDifferential l).transition i j w hw] at hc
  exact hc

/-- The local normalized integrals coincide as germs when based at the
same actual curve point. This is the compatibility required to continue
integration from one independent actual chart to the next. -/
theorem normalized_overlap (i j : ChartIndex l) (z : ℂ)
    (hz : z∈(Transition l i j).source) (f g : ℂ→ℂ)
    (hf : ∀ᶠ w in 𝓝 z,HasDerivAt f ((invariantDifferential l).coefficient i w) w)
    (hg : ∀ᶠ w in 𝓝 (Transition l i j z),
      HasDerivAt g ((invariantDifferential l).coefficient j w) w)
    (hf0 : f z=0) (hg0 : g (Transition l i j z)=0) :
    ∀ᶠ w in 𝓝 z,f w=g (Transition l i j w) := by
  filter_upwards [actual_overlap_translation l i j z hz f g hf hg] with w hw
  rw [hf0,hg0,sub_self] at hw
  exact sub_eq_zero.mp hw

/-- Construct both sides rather than postulating primitive derivatives:
every original overlap point admits actual normalized integrated
coordinates with analytic inverses whose transition is the identity germ. -/
theorem exists_compatible_integrated_coordinates (i j : ChartIndex l) (z : ℂ)
    (hz : z∈(Transition l i j).source) :
    ∃ f F g G : ℂ→ℂ,AnalyticAt ℂ f z ∧
      AnalyticAt ℂ g (Transition l i j z) ∧
      AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ G 0 ∧
      F 0=z ∧ G 0=Transition l i j z ∧
      (∀ᶠ w in 𝓝 z,F (f w)=w) ∧
      (∀ᶠ w in 𝓝 (Transition l i j z),G (g w)=w) ∧
      (∀ᶠ w in 𝓝 z,f w=g (Transition l i j w)) := by
  have htarget := (localChart l j).map_source hz.2
  obtain ⟨r,hr,_,f,F,hf0,hfa,hfd,hFa,hF0,hFl,hFr⟩:=
    exists_integrated_coordinate l i z hz.1
  obtain ⟨s,hs,_,g,G,hg0,hga,hgd,hGa,hG0,hGl,hGr⟩:=
    exists_integrated_coordinate l j (Transition l i j z) htarget
  have hf : ∀ᶠ w in 𝓝 z,HasDerivAt f ((invariantDifferential l).coefficient i w) w :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hr)) (fun w hw=>hfd w hw)
  have hg : ∀ᶠ w in 𝓝 (Transition l i j z),
      HasDerivAt g ((invariantDifferential l).coefficient j w) w :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hs)) (fun w hw=>hgd w hw)
  exact ⟨f,F,g,G,hfa z (mem_ball_self hr),hga _ (mem_ball_self hs),hFa,hGa,hF0,hG0,
    hFl,hGl,normalized_overlap l i j z hz f g hf hg hf0 hg0⟩
end LegendreIntegratedTranslations318
