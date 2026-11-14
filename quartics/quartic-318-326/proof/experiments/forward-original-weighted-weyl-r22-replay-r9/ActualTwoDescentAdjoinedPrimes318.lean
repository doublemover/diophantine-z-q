module
public import ActualTwoDescentMutualSymbolRows318
public section
noncomputable section
namespace ActualTwoDescentAdjoinedPrimes318
open ActualTwoDescentOldCorePreservation318
open scoped BigOperators
set_option maxHeartbeats 16000000

def adjoin {U J : Type*} (p : Option U → ℕ) (q : J → ℕ) : Option (U ⊕ J) → ℕ
  | none => p none
  | some (Sum.inl i) => p (some i)
  | some (Sum.inr j) => q j

instance adjoin_prime {U J : Type*} (p : Option U → ℕ) (q : J → ℕ)
    [∀ i, Fact (p i).Prime] [∀ j, Fact (q j).Prime] (i : Option (U ⊕ J)) :
    Fact (adjoin p q i).Prime := ⟨by
  cases i with
  | none => exact Fact.out
  | some i => cases i <;> exact Fact.out⟩

lemma adjoin_injective {U J : Type*} (p : Option U → ℕ) (q : J → ℕ)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hdis : ∀ i j, p i ≠ q j) : Function.Injective (adjoin p q) := by
  intro i j he
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      cases j with
      | inl j => exact False.elim (Option.none_ne_some j (hp he))
      | inr j => exact False.elim (hdis none j he)
  | some i =>
    cases i with
    | inl i =>
      cases j with
      | none => exact False.elim (Option.some_ne_none i (hp he))
      | some j =>
        cases j with
        | inl j => exact congrArg (fun i : U => some (Sum.inl i)) (Option.some.inj (hp he))
        | inr j => exact False.elim (hdis (some i) j he)
    | inr i =>
      cases j with
      | none => exact False.elim (hdis none i he.symm)
      | some j =>
        cases j with
        | inl j => exact False.elim (hdis (some j) i he.symm)
        | inr j => exact congrArg (fun j : J => some (Sum.inr j)) (hq he)

lemma adjoin_coprime {U J : Type*} (p : Option U → ℕ) (q : J → ℕ)
    (hp : ∀ i, Nat.Coprime (p i) 12) (hq : ∀ j, Nat.Coprime (q j) 12) :
    ∀ i, Nat.Coprime (adjoin p q i) 12 := by
  intro i
  cases i with
  | none => exact hp none
  | some i =>
    cases i with
    | inl i => exact hp (some i)
    | inr j => exact hq j

lemma restricted_adjoin {U J : Type*} [Fintype U] [DecidableEq U]
    [Fintype J] [DecidableEq J] (p : Option U → ℕ) (q : J → ℕ) :
    restricted (adjoin p q)=p := by
  funext i
  cases i <;> rfl
lemma adjoin_product {U J : Type*} [Fintype U] [DecidableEq U]
    [Fintype J] [DecidableEq J] (p : Option U → ℕ) (q : J → ℕ) :
    (∏ i, adjoin p q i)=(∏ i, p i)*(∏ j, q j) := by
  rw [actual_product_split,restricted_adjoin]
  rfl

end ActualTwoDescentAdjoinedPrimes318
