module
public import CTOriginalActualShaReducedPrimary318
public import Mathlib.Topology.Instances.AddCircle.Defs
public section
noncomputable section
namespace ActualTwoDescentActualShaReducedDuality318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaReducedPrimary318

/-- Precise missing global duality producer: an actual pairing on the actual finite quotient. -/
def ActualReducedDuality (n : ℚ) (hn : n ≠ 0) : Prop :=
  ∃ e : actualShaReducedPrimary n hn →* (actualShaReducedPrimary n hn →* Multiplicative (AddCircle (1 : ℚ))),
    (∀ x, e x x=1) ∧ (∀ x, (∀ y, e x y=1) → x=1)

end ActualTwoDescentActualShaReducedDuality318
