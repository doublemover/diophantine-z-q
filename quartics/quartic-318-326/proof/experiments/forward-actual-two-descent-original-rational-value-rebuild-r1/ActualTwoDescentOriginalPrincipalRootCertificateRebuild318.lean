module
public import ActualTwoDescentOriginalAllPointMeromorphicSupportRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalPrincipalRootCertificateRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- Concrete principal-function certificate on the actual original
scheme. This is deliberately not named a general principal-divisor map. -/
structure Certificate (n : K) (i : Fin 3) [Fact (n ≠ 0)] where
  function : (originalCubicScheme n).functionField
  same_function : function = ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
    (ActualTwoDescentOriginalRootIdeals318.root n i)
  nonzero : function ≠ 0
  root_order : ActualTwoDescentOriginalRootMeromorphicOrderRebuild318.value n i function = 2
  infinity_order : ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318.value n function = -2
  off_support : ∀ p : originalCubicScheme n, p ≠ rootPoint n i → p ≠ infinityPoint n →
    ∃ s : (originalCubicScheme n).presheaf.stalk p,
      IsUnit s ∧ algebraMap ((originalCubicScheme n).presheaf.stalk p)
        (originalCubicScheme n).functionField s = function

/-- Every input is produced for the SAME n, root index, scheme, field,
and coefficient embedding. n≠0 remains on the marked root DVR. -/
def certificate (n : K) (i : Fin 3) [Fact (n ≠ 0)] : Certificate n i where
  function := ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
    (ActualTwoDescentOriginalRootIdeals318.root n i)
  same_function := rfl
  nonzero := ActualTwoDescentOriginalAllPointRootSupportRebuild318.nonzero n i
  root_order := ActualTwoDescentOriginalRootMeromorphicOrderRebuild318.named_root n i
  infinity_order := ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318.named_root n _
  off_support := ActualTwoDescentOriginalOffSupportStalkUnitsRebuild318.unit n i
end ActualTwoDescentOriginalPrincipalRootCertificateRebuild318
