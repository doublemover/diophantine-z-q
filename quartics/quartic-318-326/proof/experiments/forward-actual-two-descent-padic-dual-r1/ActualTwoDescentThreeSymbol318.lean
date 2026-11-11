module
public import ActualTwoDescentPrimeLaplacian318
public import Mathlib.Tactic.NormNum.LegendreSymbol
public section
noncomputable section
namespace ActualTwoDescentThreeSymbol318
open ActualTwoDescentSymbolTable318 ActualTwoDescentSignReciprocity318
open ActualTwoDescentSupportParity318 ActualTwoDescentPrimeLaplacian318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

def lambda {ι : Type*} (p : ι → ℕ) : ι → ZMod 2 := fun i => symbolBit 3 (p i)

lemma actual_jacobi_product {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (hp : ∀ i, p i ≠ 0) (a : ℤ) :
    jacobiSym a (∏ i ∈ s, p i)=∏ i ∈ s, jacobiSym a (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,
      jacobiSym.mul_right' a (hp i) (Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)),ih]

/-- The coefficient lambda is the literal [3/p] vector, whose total
vanishes on every actual squarefree twist support11mod12. -/
theorem actual_lambda_sum {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp3 : ∀ i, p i ≠ 3)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11) : (∑ i, lambda p i)=0 := by
  have hcop (i : ι) : Nat.Coprime 3 (p i) :=
    (Nat.coprime_primes (by decide : Nat.Prime 3) Fact.out).mpr (Ne.symm (hp3 i))
  have hmod : (∏ i, p i) % 12=11 := by
    have h := congrArg ZMod.val hn
    norm_num only [ZMod.val_natCast] at h
    exact h
  have hodd : Odd (∏ i, p i) := by
    apply Nat.odd_iff.mpr
    rw [←Nat.mod_mod_of_dvd (∏ i, p i) (by decide : 2 ∣ 12),hmod]
  have hJ : jacobiSym 3 (∏ i, p i)=1 := by
    rw [jacobiSym.mod_right' 3 hodd]
    change jacobiSym 3 ((∏ i, p i) % 12)=1
    rw [hmod]
    norm_num
  apply sign_injective
  rw [sign_sum,sign_zero]
  calc
    (∏ i, sign (lambda p i)) = ∏ i, jacobiSym 3 (p i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact actual_sign_symbol 3 (p i) (hcop i)
    _ = jacobiSym 3 (∏ i, p i) :=
      (actual_jacobi_product Finset.univ p (fun i => (Fact.out : (p i).Prime).ne_zero) 3).symm
    _ = 1 := hJ

end ActualTwoDescentThreeSymbol318
