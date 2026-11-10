module
public import LegendreGlobalHolomorphicDifferential318
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public section
noncomputable section
namespace LegendreIntegratedCoordinates318
open Set Filter Metric
open scoped Topology
open LegendreCompletedComplexAtlas318 LegendreGlobalHolomorphicDifferential318
variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]

/-- Integrate the ACTUAL global differential coefficient on a genuine
small disk inside the actual chart. The primitive is normalized at the
chosen point and its derivative is the original coefficient everywhere
on that disk, not merely at the center. -/
theorem exists_primitive (i : ChartIndex l) (z : ℂ)
    (hz : z∈(localChart l i).target) :
    ∃ r : ℝ, 0<r ∧ ball z r⊆(localChart l i).target ∧
      ∃ f : ℂ→ℂ,f z=0 ∧ AnalyticOnNhd ℂ f (ball z r) ∧
        ∀w∈ball z r,HasDerivAt f ((invariantDifferential l).coefficient i w) w := by
  obtain ⟨r,hr,hsub⟩:=Metric.isOpen_iff.mp (localChart l i).open_target z hz
  have ha := (invariantDifferential l).analytic i
  have hd : DifferentiableOn ℂ ((invariantDifferential l).coefficient i) (ball z r) :=
    fun w hw=>(ha w (hsub hw)).differentiableAt.differentiableWithinAt
  obtain ⟨f,hf0,hf⟩:=hd.isExactOn_ball.with_val_at z (0:ℂ)
  have hfd : DifferentiableOn ℂ f (ball z r) :=
    fun w hw=>(hf w hw).differentiableAt.differentiableWithinAt
  exact ⟨r,hr,hsub,f,hf0,hfd.analyticOnNhd isOpen_ball,hf⟩

/-- The normalized integrated coordinate has a genuine analytic inverse.
Its derivative nonvanishing is supplied by the ACTUAL invariant form,
not assumed as an unproved local uniformization hypothesis. -/
theorem exists_integrated_coordinate (i : ChartIndex l) (z : ℂ)
    (hz : z∈(localChart l i).target) :
    ∃ r : ℝ,0<r ∧ ball z r⊆(localChart l i).target ∧
      ∃ f g : ℂ→ℂ,f z=0 ∧ AnalyticOnNhd ℂ f (ball z r) ∧
        (∀w∈ball z r,HasDerivAt f ((invariantDifferential l).coefficient i w) w) ∧
        AnalyticAt ℂ g 0 ∧ g 0=z ∧
        (∀ᶠ w in 𝓝 z,g (f w)=w) ∧ (∀ᶠ w in 𝓝 (0:ℂ),f (g w)=w) := by
  obtain ⟨r,hr,hsub,f,hf0,hfa,hfd⟩:=exists_primitive l i z hz
  have hcenter : z∈ball z r := mem_ball_self hr
  have hf := hfa z hcenter
  have hn : deriv f z≠0 := by
    rw [(hfd z hcenter).deriv]
    exact nowhere_zero l i z hz
  let g := hf.hasStrictDerivAt.localInverse f (deriv f z) z hn
  have hl : ∀ᶠ w in 𝓝 z,g (f w)=w := hf.hasStrictDerivAt.eventually_left_inverse hn
  have hga : AnalyticAt ℂ g (f z) := hf.analyticAt_localInverse hn
  have hg0 : g (f z)=z := hl.self_of_nhds
  have hr' : ∀ᶠ w in 𝓝 (f z),f (g w)=w := hf.hasStrictDerivAt.eventually_right_inverse hn
  rw [hf0] at hga hg0 hr'
  exact ⟨r,hr,hsub,f,g,hf0,hfa,hfd,hga,hg0,hl,hr'⟩

/-- Each actual point of the completed SAME Legendre curve has integrated
local coordinates. This does not yet claim their global period quotient. -/
theorem every_point_integrated (p : LegendrePlaneOverlap318.CompletedPlane l) :
    ∃ i : ChartIndex l,p∈(localChart l i).source ∧
      ∃ r : ℝ,0<r ∧ ball (localChart l i p) r⊆(localChart l i).target ∧
        ∃ f g : ℂ→ℂ,f (localChart l i p)=0 ∧
          AnalyticOnNhd ℂ f (ball (localChart l i p) r) ∧
          (∀w∈ball (localChart l i p) r,
            HasDerivAt f ((invariantDifferential l).coefficient i w) w) ∧
          AnalyticAt ℂ g 0 ∧ g 0=localChart l i p ∧
          (∀ᶠ w in 𝓝 (localChart l i p),g (f w)=w) ∧
          (∀ᶠ w in 𝓝 (0:ℂ),f (g w)=w) := by
  obtain ⟨i,hi⟩:=covers l p
  exact ⟨i,hi,exists_integrated_coordinate l i (localChart l i p)
    ((localChart l i).map_source hi)⟩
end LegendreIntegratedCoordinates318
