module
public import ActualOrderOrientationCandidates318
public section
noncomputable section
namespace ActualCommonPrimeCandidates318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 SelectedRayEmbeddings318 ActualRootSwapOrders318
open ActualOrderOrientationCandidates318
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
/-- The known divisor orientation is supplied by arithmetic tests, not assumed successful. -/
theorem card_le_two (r : Roots C u w hv) (L h0 q : ℕ) (hq : q.Prime)
    (t : Fin 3 × Fin 5 → Bool)
    (ht : ∀ i,q∣FiniteOrderSignChoices318.left
      (primaryOrder C u w hv r) (oppositeOrder C u w hv r) t i) :
    (candidates C u w hv r L h0).card≤2 :=
  FiniteOrderSignCandidates318.card_le_two _ _ _ q hq t ht
theorem nonempty_iff (r : Roots C u w hv) (L h0 q : ℕ) (hq : q.Prime)
    (t : Fin 3 × Fin 5 → Bool)
    (ht : ∀ i,q∣FiniteOrderSignChoices318.left
      (primaryOrder C u w hv r) (oppositeOrder C u w hv r) t i) :
    (candidates C u w hv r L h0).Nonempty ↔
      t∈candidates C u w hv r L h0 ∨ FiniteOrderSignChoices318.flip t∈candidates C u w hv r L h0 :=
  FiniteOrderSignCandidates318.nonempty_iff _ _ _ q hq t ht
end ActualCommonPrimeCandidates318
