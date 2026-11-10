module
public import WeierstrassHOneNonzero318
public import OriginalCharacterHOneNonzero318

public section
noncomputable section
namespace OriginalFiveHOneEquivalence318
open ActualFiveHOneDecomposition318 ActualFiveHOneRationalExhaustion318
open ActualSourceHOnePullbacks318
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

/-- The previously missing fifth-target input is discharged in its original actual H1. -/
theorem fifth_nonzero : ∃ x : TargetHOne none, x ≠ 0 :=
  ⟨WeierstrassBoundaryClass318.cohomologyClass FifthCharacterShortPolynomial318.A
      FifthCharacterShortPolynomial318.B,
    WeierstrassHOneNonzero318.cohomologyClass_nonzero _ _⟩

/-- All five target nonvanishing statements concern the original completed target schemes. -/
theorem targets_nonzero : TargetsNonzero :=
  OriginalCharacterHOneNonzero318.targets_nonzero_of_fifth fifth_nonzero

/-- The actual original five-pullback sum exhausts the whole contact H1,
with no target-nonzero or cross-transfer hypothesis. -/
theorem original_sum_bijective : Function.Bijective sumLinear :=
  OriginalCharacterHOneNonzero318.original_five_bijective fifth_nonzero

/-- Unconditional identification by the original five quotient pullbacks. -/
@[expose] def equivalence : ((i : Index) → TargetHOne i) ≃ₗ[ℚ] SourceHOne :=
  LinearEquiv.ofBijective sumLinear original_sum_bijective

theorem equivalence_apply (x : (i : Index) → TargetHOne i) :
    equivalence x = ∑ i, pullback i (x i) := rfl

/-- The inverse components are characterized by the actual source character projectors.
This statement does not identify them with the original normalized trace maps. -/
theorem inverse_component (y : SourceHOne) (i : Index) :
    pullback i (equivalence.symm y i) = ActualSourceHOneCharacterProjectors318.projector i y := by
  have h := OriginalFivePullbackIndependence318.projector_sumPullback i (equivalence.symm y)
  change ActualSourceHOneCharacterProjectors318.projector i (equivalence (equivalence.symm y)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end OriginalFiveHOneEquivalence318
