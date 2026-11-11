module
public import PELActualGeodesicPartialCharts318
public import LocalConformalEdgeExtension318
public section
noncomputable section
namespace PELActualRegularEdgeExtension318
open Set Filter
open scoped Topology
open PELMaximalActualComplexDomain318 PELActualEdgeHalfNeighborhood318
open PELActualGeodesicPartialCharts318
set_option maxHeartbeats 2800000

/-- On EVERY regular point of ALL SIX original complex geodesic edges,
a genuine holomorphic interior disk homeomorphism has a constructed
analytic extension in the SAME original complex coordinate. Its boundary
value has unit norm. The boundary extension itself is not an input, and
the original radial/Klein disk map is not used as a holomorphic map.

This consumer is universal in the genuine interior map. It does not
assert acceptance of, or import, the Riemann-mapping existence port. -/
theorem actual_regular_edge_extension
    (disk:openDomain≃ₜConformalBoundaryModulus318.UnitDisk)
    (f:ℂ→ℂ) (hf:∀q:openDomain,f q=(disk q).val)
    (hfa:AnalyticOnNhd ℂ f openDomain)
    {i:Fin 6} {z:ℂ} (hz:RegularEdge i z) :
    ∃F:ℂ→ℂ,AnalyticAt ℂ F z ∧ F=ᶠ[𝓝[openDomain] z] f ∧ ‖F z‖=1 := by
  obtain ⟨hsource,hreal,hhalf⟩ := regular_chart hz
  exact LocalConformalEdgeExtension318.local_extension openDomain openDomain_open disk f hf hfa
    (chart i) (chart_holomorphic i).1 (chart_holomorphic i).2 hsource hreal hhalf
end PELActualRegularEdgeExtension318
