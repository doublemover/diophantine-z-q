module
public import ActualOperatorNorm318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DependentFiberBundle318 FiberLinearStructure318 VectorBundleRegistration318
open HolomorphicCharts318 HolomorphicLineFactor318 LocalFrameEmbedding318
open TangentCoordinates318 ActualQuadraticForm318 TangentMetric318
open Filter Topology Bundle
open scoped Manifold ContDiff
namespace TangentMetricContinuity318
set_option maxHeartbeats 0
variable (N:ℕ) [hN:Fact (5≤N)]
local instance quotientCharts : ChartedSpace ℂ (Base (image N)) := complexChartedSpace N hN.out
local instance quotientManifold : IsManifold 𝓘(ℂ) ω (Base (image N)) := complex_manifold N hN.out

/-- The chart-invariant tangent seminorm is a genuine continuous metric on
the actual tangent bundle total space, not just isolated fiberwise norms. -/
theorem tangent_metric_continuous :
    Continuous (fun p:TangentBundle 𝓘(ℂ) (Base (image N))=>tangentSeminorm N p.proj p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  let a:=chosenLift N p₀.proj
  have ha:p₀.proj∈sheet N hN.out a:=chosenLift_mem N hN.out p₀.proj
  have ht:p₀∈(tangentFrame N a).source := by
    apply (tangentFrame N a).mem_source.mpr
    change p₀.proj∈(localChart N hN.out a).source
    rw [chart_source]
    exact ha
  have hf:ContinuousAt (fun p:TangentBundle 𝓘(ℂ) (Base (image N))=>p.proj) p₀ :=
    (FiberBundle.continuous_proj ℂ (TangentSpace 𝓘(ℂ))).continuousAt
  have he:=((quotient_localHomeomorph N hN.out).localInverseAt a).continuousAt ha
  have hi:ContinuousAt (fun p:TangentBundle 𝓘(ℂ) (Base (image N))=>
      (((quotient_localHomeomorph N hN.out).localInverseAt a) p.proj).im) p₀ :=
    UpperHalfPlane.continuous_im.continuousAt.comp (he.comp hf)
  have hc:=((tangentFrame N a).continuousAt ht).snd.norm.div (hi.const_mul 2)
    (by positivity)
  apply hc.congr_of_eventuallyEq
  have hn:∀ᶠp:TangentBundle 𝓘(ℂ) (Base (image N)) in 𝓝 p₀,p.proj∈sheet N hN.out a :=
    hf.eventually (((quotient_localHomeomorph N hN.out).localInverseAt a).open_source.mem_nhds ha)
  filter_upwards [hn] with p hp
  exact tangent_chart_length N a p.proj hp p.2

end TangentMetricContinuity318
