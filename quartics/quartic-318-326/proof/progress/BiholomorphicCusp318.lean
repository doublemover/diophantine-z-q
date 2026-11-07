module
public import ActualCuspPartialChart318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318
open PeterssonQuotient318 QuotientJ318 HighQParameter318 ActualCuspHomeomorph318
open HolomorphicCuspChart318 HolomorphicCharts318 ActualCuspPartialChart318
open scoped Manifold ContDiff
namespace BiholomorphicCusp318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The actual inverse cusp coordinate is holomorphic. Local branches of the
complex exponential are constructed by its nonzero derivative; the quotient
removes the integer-translation ambiguity. -/
theorem inverse_holomorphic (N:ℕ) (hN:5≤N) :
    letI:=complexChartedSpace N hN
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (inverseFunction N) (punctured height) := by
  letI:=complexChartedSpace N hN
  intro q hq
  obtain ⟨tau,htau⟩:=qMap_surjective height height_positive ⟨q,hq⟩
  have hparam : Periodic.qParam 1 tau=q := congrArg Subtype.val htau
  rw [←hparam]
  apply ContMDiffAt.contMDiffWithinAt
  let r := LocalQInverse318.inverse (tau:ℂ)
  have hr : AnalyticAt ℂ r (Periodic.qParam 1 tau) := LocalQInverse318.inverse_analytic tau
  have hr0 : r (Periodic.qParam 1 tau)=(tau:ℂ) := LocalQInverse318.inverse_value tau
  have hp : 0<(r (Periodic.qParam 1 tau)).im := by rw [hr0];exact tau.val.im_pos
  have hof := (UpperHalfPlane.contMDiffAt_ofComplex (n:=ω) hp).comp
    (Periodic.qParam 1 tau) hr.contDiffAt.contMDiffAt
  have hc := (HolomorphicProjection318.quotient_holomorphic N hN
    (ofComplex (r (Periodic.qParam 1 tau)))).comp (Periodic.qParam 1 tau) hof
  apply hc.congr_of_eventuallyEq
  have hh : ∀ᶠw in 𝓝 (Periodic.qParam 1 tau),height<(r w).im := by
    apply ((Complex.continuous_im.continuousAt).comp hr.continuousAt).eventually
    apply isOpen_Ioi.mem_nhds
    change height < (r (Periodic.qParam 1 tau)).im
    rw [hr0]
    exact tau.property
  filter_upwards [hh,LocalQInverse318.inverse_right (tau:ℂ)] with w hw hright
  have hpos : 0<(r w).im := lt_trans height_positive hw
  let t:UpperHalfPlane := ⟨r w,hpos⟩
  have ht:t∈high height := hw
  have hqt:Periodic.qParam 1 t=w := hright
  calc
    inverseFunction N w=inverseFunction N (Periodic.qParam 1 t) := congrArg (inverseFunction N) hqt.symm
    _ = quotientMap N t := inverseFunction_projection N ⟨t,ht⟩
    _ = quotientMap N (ofComplex (r w)) := by
      congr 1
      exact (ofComplex_apply_of_im_pos hpos).symm

/-- Both directions of the actual partial cusp chart are holomorphic in the
actual quotient complex atlas; the source and punctured-disc target are exact. -/
theorem chart_biholomorphic (N:ℕ) (hN:5≤N) :
    letI:=complexChartedSpace N hN
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (chart N) (chart N).source ∧
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (chart N).symm (chart N).target := by
  letI:=complexChartedSpace N hN
  exact ⟨coordinateFunction_holomorphic N hN,inverse_holomorphic N hN⟩

end BiholomorphicCusp318
