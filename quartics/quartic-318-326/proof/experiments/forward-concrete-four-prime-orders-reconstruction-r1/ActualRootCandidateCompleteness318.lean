module
public import ActualDenominatorCandidateReduction318
public section
noncomputable section
namespace ActualRootCandidateCompleteness318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 SelectedRayEmbeddings318 ActualOrderOrientationCandidates318
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- The finite candidates cover EVERY actual root assignment, not only a chosen Hensel branch.
The retained three coprimalities define the stated compatibility class. -/
theorem exists_iff (r : Roots C u w hv) (L h0 : ℕ) :
    (∃ t : Roots C u w hv, Compatible C u w hv t L h0) ↔
      (candidates C u w hv r L h0).Nonempty := by
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨s,hs⟩:=all_orientations C u w hv r t
    refine ⟨s,(mem_iff C u w hv r L h0 s).mpr ?_⟩
    rwa [hs]
  · rintro ⟨s,hs⟩
    exact ⟨oriented C u w hv r s,(mem_iff C u w hv r L h0 s).mp hs⟩
end ActualRootCandidateCompleteness318
