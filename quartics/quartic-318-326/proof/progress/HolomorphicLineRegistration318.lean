module
public import LinearCocycleBinding318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DependentFiberBundle318 FiberLinearStructure318 VectorBundleRegistration318
open HolomorphicCharts318 HolomorphicLineFactor318 LinearCocycleBinding318
open Filter Topology Bundle
open scoped Manifold ContDiff
namespace HolomorphicLineRegistration318
set_option maxHeartbeats 0

/-- The actual registered differential line is a holomorphic vector bundle
on the constructed complex Γ1 quotient. -/
theorem holomorphicVectorBundle (N:ℕ) [hN:Fact (5≤N)] :
    letI:=complexChartedSpace N hN.out
    ContMDiffVectorBundle ω ℂ (fibers N) 𝓘(ℂ) := by
  letI:=complexChartedSpace N hN.out
  constructor
  intro e e' he he'
  obtain ⟨a,rfl⟩:=he.out
  obtain ⟨c,rfl⟩:=he'.out
  have hf:=factor_holomorphic N hN.out a c
  have hc:=((ContinuousLinearMap.smulRightL ℂ ℂ ℂ) (ContinuousLinearMap.id ℂ ℂ)).contMDiff.comp_contMDiffOn hf
  exact hc.congr (fun b hb=>coordChange_eq N a c b hb)

/-- The genuine dependent total space, already homeomorphic to the actual
orbit quotient, now carries its constructed complex analytic manifold. -/
theorem total_complex_manifold (N:ℕ) [hN:Fact (5≤N)] :
    letI:=complexChartedSpace N hN.out
    IsManifold (𝓘(ℂ).prod 𝓘(ℂ)) ω (total N) := by
  letI:=complexChartedSpace N hN.out
  letI:=complex_manifold N hN.out
  letI:=holomorphicVectorBundle N
  infer_instance

end HolomorphicLineRegistration318
