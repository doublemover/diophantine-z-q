module
public import ActualTwoDescentCirclePrimaryInfinite318
public section
noncomputable section
namespace ActualTwoDescentCirclePrimaryPruefer318
set_option maxHeartbeats 16000000
open ActualTwoDescentCirclePrimaryInvolutions318 ActualTwoDescentCirclePrimaryInfinite318
open ActualTwoDescentPrueferClassification318 ActualTwoDescentDyadicPrueferModel318

lemma actual_circle_primary_pruefer : Nonempty (CirclePrimary ≃* PrueferTwo) := by
  letI := actual_circle_primary_infinite
  obtain ⟨hf,hc⟩ := actual_circle_primary_two_bound
  exact actual_infinite_primary_pruefer CommGroup.primaryComponent.isPGroup hf hc

/-- Actual complex-circle primary torsion is identified with the actual
rational-circle dyadic subgroup, not with an abstract placeholder. -/
def circlePrimaryPrueferEquiv : CirclePrimary ≃* PrueferTwo :=
  Classical.choice actual_circle_primary_pruefer

end ActualTwoDescentCirclePrimaryPruefer318
