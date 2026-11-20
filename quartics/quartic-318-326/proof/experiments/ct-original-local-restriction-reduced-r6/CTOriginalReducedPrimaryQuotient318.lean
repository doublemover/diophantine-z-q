module
public import CTOriginalStablePrimaryCore318
public import Mathlib.GroupTheory.QuotientGroup.Basic
public section
noncomputable section
namespace ActualTwoDescentReducedPrimaryQuotient318
set_option maxHeartbeats 16000000

open ActualTwoDescentStablePrimaryCore318
variable (G : Type*) [CommGroup G]

abbrev reducedPrimary := G ⧸ stableTwoCore G

end ActualTwoDescentReducedPrimaryQuotient318
