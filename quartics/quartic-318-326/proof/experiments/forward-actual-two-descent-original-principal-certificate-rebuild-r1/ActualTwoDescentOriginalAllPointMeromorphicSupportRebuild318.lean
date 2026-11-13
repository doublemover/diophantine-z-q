module
public import ActualTwoDescentOriginalInfinityMeromorphicOrderRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalAllPointMeromorphicSupportRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- At EVERY off-support scheme point the actual stalk unit is produced.
If its stalk is a DVR, its normalized valuation is therefore zero. The
DVR premise here is explicit, not silently deduced for all scheme points. -/
theorem value_zero (n : K) (i : Fin 3) (p : originalCubicScheme n)
    [IsDiscreteValuationRing ((originalCubicScheme n).presheaf.stalk p)]
    (hr : p ≠ rootPoint n i) (ho : p ≠ infinityPoint n) :
    ActualDvrMeromorphicOrder318.value ((originalCubicScheme n).presheaf.stalk p)
      (originalCubicScheme n).functionField
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i)) = 0 := by
  obtain ⟨s,hs,hf⟩ := ActualTwoDescentOriginalOffSupportStalkUnitsRebuild318.unit n i p hr ho
  rw [←hf]
  exact ActualDvrMeromorphicOrder318.value_unit _ _ s hs

/-- The inverse uses the SAME actual stalk embedding, including at
non-rational points. No finite test of closed points is substituted. -/
theorem inverse_unit (n : K) (i : Fin 3) (p : originalCubicScheme n)
    (hr : p ≠ rootPoint n i) (ho : p ≠ infinityPoint n) :
    ∃ s : ((originalCubicScheme n).presheaf.stalk p)ˣ,
      algebraMap ((originalCubicScheme n).presheaf.stalk p) (originalCubicScheme n).functionField
        (s : (originalCubicScheme n).presheaf.stalk p) =
      (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
        (ActualTwoDescentOriginalRootIdeals318.root n i))⁻¹ := by
  obtain ⟨s,hs,hf⟩ := ActualTwoDescentOriginalOffSupportStalkUnitsRebuild318.unit n i p hr ho
  obtain ⟨u,hu⟩ := hs
  refine ⟨u⁻¹, ?_⟩
  rw [map_units_inv,hu,hf]
end ActualTwoDescentOriginalAllPointMeromorphicSupportRebuild318
