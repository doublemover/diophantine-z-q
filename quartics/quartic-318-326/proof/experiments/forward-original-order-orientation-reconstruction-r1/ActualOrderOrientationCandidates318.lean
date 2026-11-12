module
public import ActualRootSwapOrders318
public section
noncomputable section
namespace ActualOrderOrientationCandidates318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 SelectedRayEmbeddings318 ActualRootSwapOrders318
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
@[expose] def Extra (r : Roots C u w hv) (L h0 : ℕ) (s : Fin 3 × Fin 5 → Bool) : Prop :=
  let t := oriented C u w hv r s
  Nat.Coprime (product C u w) (plus C u w hv t) ∧
  Nat.Coprime (plus C u w hv t) L ∧ Nat.gcd ((product C u w)^3*minus C u w hv t) L∣h0
@[expose] def Compatible (r : Roots C u w hv) (L h0 : ℕ) : Prop :=
  Nat.Coprime (minus C u w hv r) (plus C u w hv r) ∧
  Nat.Coprime (product C u w) (plus C u w hv r) ∧
  Nat.Coprime (plus C u w hv r) L ∧ Nat.gcd ((product C u w)^3*minus C u w hv r) L∣h0
@[expose] def candidates (r : Roots C u w hv) (L h0 : ℕ) : Finset (Fin 3 × Fin 5 → Bool) :=
  FiniteOrderSignCandidates318.candidates (primaryOrder C u w hv r) (oppositeOrder C u w hv r)
    (Extra C u w hv r L h0)
lemma mem_iff (r : Roots C u w hv) (L h0 : ℕ) (s : Fin 3 × Fin 5 → Bool) :
    s∈candidates C u w hv r L h0 ↔ Compatible C u w hv (oriented C u w hv r s) L h0 := by
  rw [candidates,FiniteOrderSignCandidates318.mem_iff,←minus_swap,←plus_swap]
  rfl
/-- An actual successful finite candidate gives the same original three CRT residues. -/
theorem witness (r : Roots C u w hv) (L h0 : ℕ) (s : Fin 3 × Fin 5 → Bool)
    (hs : s∈candidates C u w hv r L h0) :
    let t := oriented C u w hv r s
    ∃ h : ℕ, Nat.ModEq ((product C u w)^3*minus C u w hv t) h 0 ∧
      Nat.ModEq (plus C u w hv t) h 1 ∧ Nat.ModEq L h h0 ∧
      SelectedTraceFromOrders318.Orders C u w hv (minus C u w hv t) (plus C u w hv t) := by
  obtain ⟨hmp,hPm,hpL,hc⟩:=(mem_iff C u w hv r L h0 s).mp hs
  exact ActualOrderContinuityCRT318.witness C u w hv _ L h0 hPm hmp hpL hc
end ActualOrderOrientationCandidates318
