module
public import ActualTwoDescentTwistDomain318
public section
noncomputable section
namespace ActualTwoDescentSymbolTable318
open ActualTwoDescentPrimeFamily318 ActualTwoDescentResidueBits318
open ActualTwoDescentFamilyReciprocity318 ActualTwoDescentFamilyProducts318
open ActualTwoDescentTwistDomain318
set_option maxHeartbeats 16000000

def symbolBit (a b : ℕ) : ZMod 2 := if jacobiSym (a : ℤ) b = -1 then 1 else 0
def boolBit (b : Bool) : ZMod 2 := if b then 1 else 0

lemma actual_bit_of_sign (a b : ℕ) (t : Bool)
    (h : jacobiSym (a : ℤ) b=bitSign t) : symbolBit a b=boolBit t := by
  rw [symbolBit,h]
  cases t <;> norm_num [bitSign,boolBit]

/-- Actual directed F2 symbol entries, at the produced primes, not a
second matrix assumed to have the prescribed entries. -/
theorem actual_symbol_table {ι : Type*} (p : ι → ℕ)
    (oldBits : ℕ → ι → Bool) (newBits : ℕ → ℕ → Bool)
    (special : ℕ → Bool) (forbidden : Finset ℕ) (N k : ℕ)
    (F : PrimeFamily p oldBits newBits special forbidden N k) :
    (∀ i j, symbolBit (F.value i) (p j)=boolBit (oldBits i.val j)) ∧
    (∀ i j, j.val < i.val →
      symbolBit (F.value i) (F.value j)=boolBit (newBits i.val j.val)) := by
  constructor
  · intro i j
    exact actual_bit_of_sign _ _ _ (F.old_symbol i j)
  · intro i j hji
    exact actual_bit_of_sign _ _ _ (F.earlier_symbol i j hji)

/-- The retained preparation congruences17 and1 modulo24 feed the actual
finite prime producer and both twist domains without a new residue premise.
The constructed symbol tables and twist parameters refer to the SAME F. -/
theorem actual_prepared_twists (β θ : ℕ) (hsq : Squarefree (β*θ))
    (hβ : (β : ZMod 24)=17) (hθ : (θ : ZMod 24)=1)
    (oldBits : ℕ → Support (β*θ) → Bool) (newBits : ℕ → ℕ → Bool)
    (forbidden : Finset ℕ) (N d : ℕ) :
    ∃ F : PrimeFamily (supportPrime (β*θ)) oldBits newBits
      (fun i => decide (i=d)) forbidden N (d+1),
      TwistDomain β θ (β*multiplier F) ∧
      N < β*multiplier F ∧ N < (β*multiplier F)*θ ∧
      Nat.Coprime (multiplier F) (β*θ) ∧
      (∀ i j, symbolBit (F.value i) (supportPrime (β*θ) j)=boolBit (oldBits i.val j)) ∧
      (∀ i j, j.val < i.val →
        symbolBit (F.value i) (F.value j)=boolBit (newBits i.val j.val)) := by
  have hβ12 : (β : ZMod 12)=5 := by
    have h := congrArg (ZMod.castHom (by decide : 12 ∣ 24) (ZMod 12)) hβ
    norm_num only [map_natCast, map_ofNat] at h
    exact h
  have hθ12 : (θ : ZMod 12)=1 := by
    have h := congrArg (ZMod.castHom (by decide : 12 ∣ 24) (ZMod 12)) hθ
    simpa only [map_natCast,map_one] using h
  obtain ⟨F,hF,hN,hNt,hcop⟩ := actual_twist_domain β θ hsq hβ12 hθ12 oldBits newBits forbidden N d
  obtain ⟨ho,hn⟩ := actual_symbol_table _ _ _ _ _ _ _ F
  exact ⟨F,hF,hN,hNt,hcop,ho,hn⟩

end ActualTwoDescentSymbolTable318
