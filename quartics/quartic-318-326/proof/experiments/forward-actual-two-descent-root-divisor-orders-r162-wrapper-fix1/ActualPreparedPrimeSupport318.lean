module
public import ActualPreparedMutualSymbolConversion318
public import ActualTwoDescentSmallPattern318
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Option
public section
noncomputable section
namespace ActualPreparedPrimeSupport318
open scoped BigOperators
open ActualTwoDescentSmallPattern318

/-- Enumerate the literal distinct prime divisors, with their exact product.
The empty theta support when n=1 is included without adding a dummy prime. -/
theorem prime_support_product (n : ℕ) (hs : Squarefree n) :
    (∏ p : ↥n.primeFactors, (p:ℕ))=n := by
  rw [Finset.prod_coe_sort,Nat.prod_primeFactors_of_squarefree hs]

/-- A nontrivial squarefree beta admits exactly the nonempty Option(Fin d)
index shape expected by the existing simultaneous construction. This is an
enumeration of its actual primes, not a replacement squareclass. -/
theorem beta_support (beta : ℕ) (hs : Squarefree beta) (hb : 1<beta) :
    ∃ (d : ℕ) (qB : BetaIndex d → ℕ),
      (∀ i, (qB i).Prime) ∧ Function.Injective qB ∧
      (∏ i, qB i)=beta ∧ (∀ i, qB i∣beta) := by
  classical
  have hne : beta.primeFactors.Nonempty := by
    by_contra h
    have he : beta.primeFactors=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hp := Nat.prod_primeFactors_of_squarefree hs
    rw [he,Finset.prod_empty] at hp
    omega
  let B := ↥beta.primeFactors
  haveI : Nonempty B := by
    obtain ⟨p,hp⟩ := hne
    exact ⟨⟨p,hp⟩⟩
  have hc : 0<Fintype.card B := Fintype.card_pos
  let d := Fintype.card B-1
  let e : BetaIndex d ≃ B := Fintype.equivOfCardEq (by
    change Fintype.card (Option (Fin d))=Fintype.card B
    rw [Fintype.card_option,Fintype.card_fin]
    dsimp [d]
    omega)
  let qB : BetaIndex d → ℕ := fun i => (e i).val
  refine ⟨d,qB,?_,?_,?_,?_⟩
  · intro i
    exact Nat.prime_of_mem_primeFactors (e i).property
  · intro i j hij
    apply e.injective
    exact Subtype.ext hij
  · calc
      (∏ i, qB i)=(∏ p : B, (p:ℕ)) := e.prod_comp (fun p : B => (p:ℕ))
      _=beta := prime_support_product beta hs
  · intro i
    exact Nat.dvd_of_mem_primeFactors (e i).property

/-- Disjointness is inherited from coprimality of the actual coefficient
products, rather than inserted as a choice of unrelated prime arrays. -/
theorem support_disjoint {B J : Type*} (beta theta : ℕ)
    (qB : B → ℕ) (qJ : J → ℕ)
    (hB : ∀ i, (qB i).Prime) (hBd : ∀ i, qB i∣beta)
    (hJd : ∀ j, qJ j∣theta) (hc : Nat.Coprime beta theta) :
    ∀ i j, qB i≠qJ j := by
  intro i j he
  have hunit : Nat.Coprime (qB i) (qB i) :=
    (hc.of_dvd_left (hBd i)).of_dvd_right (by rw [he]; exact hJd j)
  have hone : qB i=1 := by
    simpa only [Nat.Coprime,Nat.gcd_self] using hunit
  exact (hB i).ne_one hone

end ActualPreparedPrimeSupport318
