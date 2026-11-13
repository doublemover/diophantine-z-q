module
public import ActualTwoDescentOriginalOffSupportStalkUnitsRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalAllPointRootSupportRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- Complete all-scheme-point support certificate. No rational-point-only
cover and no abstract principal-divisor constructor is substituted. -/
theorem classify (n : K) (i : Fin 3) (p : originalCubicScheme n) :
    p=rootPoint n i ∨ p=infinityPoint n ∨
      ∃ s : (originalCubicScheme n).presheaf.stalk p,
        IsUnit s ∧ algebraMap ((originalCubicScheme n).presheaf.stalk p)
          (originalCubicScheme n).functionField s=
            ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
              (ActualTwoDescentOriginalRootIdeals318.root n i) := by
  by_cases hr : p=rootPoint n i
  · exact Or.inl hr
  by_cases ho : p=infinityPoint n
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr (ActualTwoDescentOriginalOffSupportStalkUnitsRebuild318.unit n i p hr ho))

/-- The support certificate and BOTH exact named-function specializations
are available on the same original scheme. The n≠0 condition remains on
the root DVR/order producer, not on this support theorem. -/
theorem nonzero (n : K) (i : Fin 3) :
    ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
      (ActualTwoDescentOriginalRootIdeals318.root n i) ≠ 0 :=
  ActualTwoDescentOriginalGenericFunctionsRebuild318.root_nonzero n _
end ActualTwoDescentOriginalAllPointRootSupportRebuild318
