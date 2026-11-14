module
public import ActualOriginalArchimedeanChartInput318
public section
noncomputable section
namespace ActualGraphCompactSupport318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318
set_option maxHeartbeats 16000000

/-- Compactness is pulled back along the actual original graph using its
actual coordinate projection. An arbitrary continuous preimage of a compact
set would not suffice. -/
theorem actual_graph_compact_support (κ : ℝ) (W : Coordinates ℝ→ℝ)
    (hW : HasCompactSupport W) : HasCompactSupport (fun v => W (graph κ v)) := by
  have hK : IsCompact (projection '' tsupport W) := hW.isCompact.image projection_continuous
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro v hv
  refine ⟨graph κ v,?_,projection_graph κ v⟩
  exact subset_closure hv

end ActualGraphCompactSupport318
