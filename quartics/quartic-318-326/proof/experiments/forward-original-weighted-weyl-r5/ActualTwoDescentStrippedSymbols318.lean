module
public import ActualTwoDescentPrimeMonomials318
public section
noncomputable section
namespace ActualTwoDescentStrippedSymbols318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentSignReciprocity318
open ActualTwoDescentSymbolTable318 ActualTwoDescentSupportParity318
open ActualTwoDescentPrimeLaplacian318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sign_mul_bit (a b : ZMod 2) : sign (a*b)=(sign a)^b.val := by
  fin_cases a <;> fin_cases b <;> norm_num [sign]

/-- The actual q-free integer factor of the squarefree representative. -/
def stripped (p : ι → ℕ) (u : ι → ZMod 2) (i : ι) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, p j ^ (u j).val

lemma actual_stripped_factor (p : ι → ℕ) (u : ι → ZMod 2) (i : ι) :
    monomial p u=(p i)^(u i).val*stripped p u i := by
  exact (Finset.mul_prod_erase Finset.univ (fun j => p j^(u j).val) (Finset.mem_univ i)).symm

lemma actual_weighted_jacobi (s : Finset ι) (p : ι → ℕ) (u : ι → ZMod 2) (q : ℕ)
    (hc : ∀ i ∈ s, Nat.Coprime (p i) q) :
    jacobiSym ((∏ i ∈ s, p i^(u i).val : ℕ) : ℤ) q=
      sign (∑ i ∈ s, symbolBit (p i) q*u i) := by
  induction s using Finset.induction_on with
  | empty => simp [sign_zero]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Nat.cast_mul,jacobiSym.mul_left,Finset.sum_insert hi,sign_add]
    rw [ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))]
    rw [Nat.cast_pow,jacobiSym.pow_left,←actual_sign_symbol _ _ (hc i (Finset.mem_insert_self i s)),
      sign_mul_bit]

/-- Actual Jacobi symbols of the stripped representatives equal the exact
weighted row sums of the same prime-symbol matrix. -/
theorem actual_stripped_symbol (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (u : ι → ZMod 2) (i : ι) :
    jacobiSym (stripped p u i : ℤ) (p i)=sign ((edges p *ᵥ u) i) := by
  rw [stripped,actual_weighted_jacobi]
  · congr 1
    rw [Matrix.mulVec,dotProduct]
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [edges,ite_true,zero_mul,add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [Ne.symm hji,ite_false]
  · intro j hj
    exact (Nat.coprime_primes Fact.out Fact.out).mpr
      (fun he => (Finset.mem_erase.mp hj).1 (hd he))

lemma actual_stripped_coprime (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (u : ι → ZMod 2) (i : ι) :
    Nat.Coprime (stripped p u i) (p i) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro j hj
  apply Nat.Coprime.pow_left
  exact (Nat.coprime_primes Fact.out Fact.out).mpr
    (fun he => (Finset.mem_erase.mp hj).1 (hd he))

end ActualTwoDescentStrippedSymbols318
