module
public import CTOriginalActualShaPrimary318
public import CTOriginalReducedPrimaryQuotient318
public section
noncomputable section
namespace ActualTwoDescentActualShaReducedPrimary318
set_option maxHeartbeats 16000000


open ActualTwoDescentActualShaPrimary318 ActualTwoDescentStablePrimaryCore318
open ActualTwoDescentReducedPrimaryQuotient318

abbrev actualShaDivisibleCore (n : ℚ) (hn : n ≠ 0) := stableTwoCore (actualShaPrimary n hn)
abbrev actualShaReducedPrimary (n : ℚ) (hn : n ≠ 0) := reducedPrimary (actualShaPrimary n hn)

end ActualTwoDescentActualShaReducedPrimary318
