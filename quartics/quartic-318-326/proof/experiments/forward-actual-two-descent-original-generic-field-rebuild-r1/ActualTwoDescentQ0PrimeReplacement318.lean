module
public import ActualTwoDescentQ0CoreReplacement318
public section
noncomputable section
namespace ActualTwoDescentQ0PrimeReplacement318
open ActualTwoDescentPrescribedPrime318 ActualTwoDescentSmallPrimeAssembly318
open ActualTwoDescentSymbolTable318 ActualTwoDescentPrimeLaplacian318
open ActualTwoDescentQ0CoreReplacement318 ActualTwoDescentMatrixCompletion318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

/-- An actual new q0 prime realizes every requested diagonal toggle while
all other prime VALUES remain unchanged. This is not a formal matrix edit. -/
theorem actual_q0_prime_replacement {U : Type*} [Fintype U] [DecidableEq U]
    (p : Option U → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hc : ∀ i, Nat.Coprime (p i) 12) (htype : (p none : ZMod 12)=7)
    (hn : ((∏ i, p i : ℕ) : ZMod 12)=11)
    (t : U → ZMod 2) (forbidden : Finset ℕ) (N : ℕ) :
    ∃ p' : Option U → ℕ,
      (∀ i, (p' i).Prime) ∧ Function.Injective p' ∧
      (∀ i, p' (some i)=p (some i)) ∧
      N < p' none ∧ p' none ∉ forbidden ∧ p' none ≠ p none ∧
      (p' none : ZMod 12)=7 ∧ ((∏ i, p' i : ℕ) : ZMod 12)=11 ∧
      (∀ i, edges p' (some i) none=edges p (some i) none+t i) := by
  classical
  let q : U → ℕ := fun i => p (some i)
  have hq : Function.Injective q := fun i j h => Option.some.inj (hd h)
  have hq2 : ∀ i, q i ≠ 2 := by
    intro i he
    have h := hc (some i)
    change Nat.Coprime (q i) 12 at h
    rw [he] at h
    norm_num at h
  let bits : U → Bool := fun i => encode (edges p (some i) none+t i)
  obtain ⟨r,hr,hprime,havoid,hfresh,hrtype,hrbits⟩ := actual_prescribed_prime q hq
    (fun i => hc (some i)) hq2 bits true (insert (p none) forbidden) N
  let p' : Option U → ℕ := fun i => match i with
    | none => r
    | some i => p (some i)
  have hpinj : Function.Injective p' := by
    intro i j he
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact False.elim (hfresh j he)
    | some i =>
      cases j with
      | none => exact False.elim (hfresh i he.symm)
      | some j => exact hd he
  have hptype : (p' none : ZMod 12)=7 := hrtype
  have hpmod : ((∏ i, p' i : ℕ) : ZMod 12)=11 := by
    rw [Fintype.prod_option,Nat.cast_mul,hptype]
    have hold := hn
    rw [Fintype.prod_option,Nat.cast_mul,htype] at hold
    exact hold
  refine ⟨p',?_,hpinj,fun _ => rfl,hr,?_,?_,hptype,hpmod,?_⟩
  · intro i
    cases i with
    | none => exact hprime
    | some i => exact Fact.out
  · intro h
    exact havoid (Finset.mem_insert_of_mem h)
  · intro h
    apply havoid
    rw [show r=p none from h]
    exact Finset.mem_insert_self _ _
  · intro i
    have hj : jacobiSym (r : ℤ) (q i)=
        ActualTwoDescentResidueBits318.bitSign (bits i) := by
      rw [←legendreSym.to_jacobiSym]
      simpa only [legendreSym,Int.cast_natCast] using hrbits i
    have hs := actual_bit_of_sign r (q i) (bits i) hj
    simpa only [edges,p',q,Option.some_ne_none,if_false,bits,boolBit_encode] using hs

end ActualTwoDescentQ0PrimeReplacement318
