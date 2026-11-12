module
public import ActualTwoDescentQ0BetaPreservation318
public section
noncomputable section
namespace ActualTwoDescentMutualSymbolRows318
open ActualTwoDescentSignReciprocity318 ActualTwoDescentSymbolTable318
open ActualTwoDescentSupportParity318
open scoped BigOperators
set_option maxHeartbeats 16000000

lemma actual_jacobi_numerator_product {ι : Type*} (s : Finset ι) (p : ι → ℕ) (q : ℕ) :
    jacobiSym ((∏ i ∈ s, p i : ℕ) : ℤ) q=∏ i ∈ s, jacobiSym (p i : ℤ) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Nat.cast_mul,jacobiSym.mul_left,Finset.prod_insert hi,ih]

/-- A square PRODUCT at one original prime gives the required zero row
sum. No unjustified individual square-symbol condition is substituted. -/
theorem actual_symbol_row_zero {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (q : ℕ) (hc : ∀ i, Nat.Coprime (p i) q)
    (hs : jacobiSym ((∏ i, p i : ℕ) : ℤ) q=1) :
    (∑ i, symbolBit (p i) q)=0 := by
  apply sign_injective
  rw [sign_sum,sign_zero]
  calc
    (∏ i, sign (symbolBit (p i) q))=∏ i, jacobiSym (p i : ℤ) q := by
      apply Finset.prod_congr rfl
      intro i _
      exact actual_sign_symbol _ _ (hc i)
    _=jacobiSym ((∏ i, p i : ℕ) : ℤ) q :=
      (actual_jacobi_numerator_product Finset.univ p q).symm
    _=1 := hs

/-- Literal mutual-square symbol premises for the original beta/theta
products, before adding ANY auxiliary prime. -/
structure MutualSymbols {B J : Type*} [Fintype B] [Fintype J]
    (qB : B → ℕ) (qJ : J → ℕ) : Prop where
  theta_at_beta : ∀ b, jacobiSym ((∏ j, qJ j : ℕ) : ℤ) (qB b)=1
  beta_at_theta : ∀ j, jacobiSym ((∏ b, qB b : ℕ) : ℤ) (qJ j)=1

/-- Both directed old-support row sums vanish at the SAME original
products. Quadratic reciprocity is not used to replace either premise. -/
theorem actual_mutual_rows {B J : Type*} [Fintype B] [Fintype J]
    (qB : B → ℕ) (qJ : J → ℕ) [∀ b, Fact (qB b).Prime] [∀ j, Fact (qJ j).Prime]
    (hdis : ∀ b j, qB b ≠ qJ j) (H : MutualSymbols qB qJ) :
    (∀ b, (∑ j, symbolBit (qJ j) (qB b))=0) ∧
    (∀ j, (∑ b, symbolBit (qB b) (qJ j))=0) := by
  constructor
  · intro b
    apply actual_symbol_row_zero qJ (qB b) _ (H.theta_at_beta b)
    intro j
    exact (Nat.coprime_primes Fact.out Fact.out).mpr (Ne.symm (hdis b j))
  · intro j
    apply actual_symbol_row_zero qB (qJ j) _ (H.beta_at_theta j)
    intro b
    exact (Nat.coprime_primes Fact.out Fact.out).mpr (hdis b j)

end ActualTwoDescentMutualSymbolRows318
