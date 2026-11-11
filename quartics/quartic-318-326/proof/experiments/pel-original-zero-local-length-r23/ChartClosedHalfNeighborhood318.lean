module
public import RealSeamNeighborhood318
public section
namespace ChartClosedHalfNeighborhood318
open Set Filter
open scoped Topology
/-- The actual open-side chart identity determines the closed side too.
At EVERY nearby real seam point use actual interior approaches, not an
assumed closed-chart or boundary parameterization. -/
theorem closed_side (D:Set ℂ) (hD:IsOpen D) (e:OpenPartialHomeomorph ℂ ℂ)
    {z:ℂ} (hz:z∈e.source)
    (hh:∀ᶠw in 𝓝 (e z),e.symm w∈D ↔0<w.im) :
    ∀ᶠy in 𝓝 z,0≤(e y).im → y∈closure D := by
  let S:Set ℂ:={w|e.symm w∈D ↔0<w.im}
  have he:e z∈interior S:=mem_interior_iff_mem_nhds.mpr hh
  have hnear:∀ᶠy in 𝓝 z,e y∈interior S :=
    (e.continuousAt hz).eventually (isOpen_interior.mem_nhds he)
  filter_upwards [e.open_source.mem_nhds hz,hnear] with y hy hyS hy0
  have hyhalf:∀ᶠw in 𝓝 (e y),e.symm w∈D ↔0<w.im :=
    mem_of_superset (isOpen_interior.mem_nhds hyS) interior_subset
  rcases lt_or_eq_of_le hy0 with hpos|heq
  · have hD':e.symm (e y)∈D := (interior_subset hyS).mpr hpos
    exact subset_closure (by simpa only [e.left_inv hy] using hD')
  · have hfront:=RealSeamNeighborhood318.chart_seam_frontier D hD e
      (e.map_source hy) heq.symm hyhalf
    simpa only [e.left_inv hy] using hfront.1
end ChartClosedHalfNeighborhood318
