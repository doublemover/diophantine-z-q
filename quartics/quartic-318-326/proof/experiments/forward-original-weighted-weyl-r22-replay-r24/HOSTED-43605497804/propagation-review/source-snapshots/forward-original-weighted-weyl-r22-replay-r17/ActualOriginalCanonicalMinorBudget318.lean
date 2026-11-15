module
public import ActualOriginalCanonicalSliceBudget318
public section
noncomputable section
namespace ActualOriginalCanonicalMinorBudget318
open QuadricCRTAssembly318 ActualOriginalCanonicalSupportBox318
open ActualOriginalCanonicalSliceBudget318 ActualOriginalMinorCorrelationIntegral318
open ActualOriginalCompactCircleCount318 ActualOriginalMajorArcDomain318
open ActualOriginalCircleMinorArcIdentity318 MeasureTheory

/-- A single support radius is produced from the actual compact weight.
Any later bound on the explicit COMPLETE slice budget controls the SAME
original minor integral. The power-saving budget itself is still required. -/
theorem actual_compact_minor_slice_budget (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hc : HasCompactSupport W) :
    ∃ R : ℝ, 1≤R ∧ ∀ B : ℝ, 0<B → ∀ N : ℕ, ∀ C : ℝ, 0≤C →
      (∀ θ∈minorDomain N B,
        canonicalSliceBudget κ ⌈R*B⌉ (latticeWeight B W) (θ : AddCircle (1 : ℝ))≤C^2) →
      ‖minorArcIntegral κ N B W‖≤C*volume.real (minorDomain N B) := by
  obtain ⟨R,hR,hs⟩ := actual_compact_support_radius W hc
  refine ⟨R,hR,fun B hB N C hC hbudget => ?_⟩
  apply actual_minor_integral_of_correlation_budget κ N B W (centeredBox ⌈R*B⌉)
    (actual_scaled_support_box W R B hB hs) C hC
  intro θ hθ
  exact (actual_correlation_le_canonical_slices κ ⌈R*B⌉ (latticeWeight B W)
    (θ : AddCircle (1 : ℝ))).trans (hbudget θ hθ)

end ActualOriginalCanonicalMinorBudget318
