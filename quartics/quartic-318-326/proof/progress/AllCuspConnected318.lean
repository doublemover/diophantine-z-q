module
public import AllCuspEmbeddings318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 PeterssonQuotient318
open FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 HolomorphicCharts318 AllCuspCharts318
open scoped Manifold ContDiff
namespace AllCuspConnected318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem original_connected (N:ℕ) : ConnectedSpace (Base (image N)) := inferInstance

/-- The compactified analytic curve is connected because the actual original
quotient is connected and its open embedding has dense range. -/
theorem filled_connected (N:ℕ) (hN:5≤N) : ConnectedSpace (Filled N hN) := by
  letI:ConnectedSpace (Base (image N)):=original_connected N
  letI:PreconnectedSpace (Filled N hN):=
    (AllCuspHausdorff318.original_dense N hN).preconnectedSpace (original_openEmbedding N hN).continuous
  exact ⟨⟨original N hN (GammaOneAtlas318.quotientMap N ⟨Complex.I,by simp⟩)⟩⟩

/-- Actual compact connected complex analytic source, on its genuine gluing
topology, with no algebraic comparison premise. -/
theorem compact_connected_complex_curve (N:ℕ) (hN:5≤N) :
    letI:=filledChartedSpace N hN
    IsManifold 𝓘(ℂ) ω (Filled N hN) ∧ CompactSpace (Filled N hN) ∧
      T2Space (Filled N hN) ∧ SecondCountableTopology (Filled N hN) ∧ ConnectedSpace (Filled N hN) := by
  letI:=filledChartedSpace N hN
  exact ⟨AllCuspComplexCurve318.filled_isManifold N hN,AllCuspCompact318.filled_compactSpace N hN,
    AllCuspHausdorff318.filled_t2 N hN,filled_secondCountable N hN,filled_connected N hN⟩

end AllCuspConnected318
