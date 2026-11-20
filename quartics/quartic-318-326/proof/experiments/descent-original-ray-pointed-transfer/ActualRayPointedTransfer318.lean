module
public import ActualRayPeriod16Interface318
public import ActualRayPointedAnchor318
import all ActualRayPeriod16Interface318
public section
noncomputable section
namespace ActualRayPointedTransfer318

open OriginalInteriorTelescoping318 ActualRayPeriod16Interface318
open ActualRayPointedAnchor318

/-- Narrow form of the remaining nonlinear input: one actual thin
one-sequence pairing for every distinguished original prime. The cube
assumption is already independently produced at the same Y. No estimate
at a fixed y, unrelated nilsequence, full two-dimensional box or
uniform-in-selector-field claim is implied. -/
def AnchorOnDiagonal (H : Family) (Y : ℕ→ℕ) (a : ℕ)
    (qMax : ℕ→ℕ) (jMin jMax : ℕ→ℕ→ℕ) (delta eps : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N≥N₀, ∀ r∈H.rows (Y N) N,
    LinearBudget r a (qMax (Y N)) (jMin (Y N) N) (jMax (Y N) N) delta →
    ∃ hn : 0<r.n, AnchorBudget r hn eps

theorem pointed_transfer_of_anchors (H : Family) (Y : ℕ→ℕ) (a : ℕ)
    (qMax : ℕ→ℕ) (jMin jMax : ℕ→ℕ→ℕ) (delta eps : ℝ)
    (anchor : AnchorOnDiagonal H Y a qMax jMin jMax delta eps) :
    PointedTransferOnDiagonal H Y a qMax jMin jMax delta eps := by
  obtain ⟨N₀,h⟩ := anchor
  refine ⟨N₀,?_⟩
  intro N hN r hr hc
  obtain ⟨hn,ha⟩ := h N hN r hr hc
  simpa only [mul_assoc] using mixed_of_anchor r hn eps ha

theorem actual_mixed_of_common_anchors (H : Family) (Y : ℕ→ℕ) (a : ℕ)
    (qMax : ℕ→ℕ) (jMin jMax : ℕ→ℕ→ℕ) (delta eps : ℝ)
    (linear : LinearOnDiagonal H Y a qMax jMin jMax delta)
    (anchor : AnchorOnDiagonal H Y a qMax jMin jMax delta eps) :
    ∃ N₀ : ℕ,∀ N≥N₀,∀ r∈H.rows (Y N) N,
      MixedBudget r (eps*((r.n:ℝ)*(r.M:ℝ))) := by
  simpa only [mul_assoc] using
    actual_mixed_on_common_diagonal H Y a qMax jMin jMax delta eps linear
      (pointed_transfer_of_anchors H Y a qMax jMin jMax delta eps anchor)

end ActualRayPointedTransfer318
