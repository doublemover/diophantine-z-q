module
public import ActualTwoDescentPointExtraction318
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public section
noncomputable section
namespace ActualTwoDescentFreshPrime318
set_option maxHeartbeats 16000000

/-- The simultaneous old-support residue and new mod12 type are merged
as an actual unit of the product residue ring. This is the CRT input used
by the prime producer, not an assumption that compatible primes exist. -/
def mergedUnit (m n : ℕ) (hmn : Nat.Coprime m n)
    (u : (ZMod m)ˣ) (v : (ZMod n)ˣ) : (ZMod (m*n))ˣ := by
  let uv : (ZMod m × ZMod n)ˣ :=
    { val := ((u : ZMod m),(v : ZMod n))
      inv := ((↑u⁻¹ : ZMod m),(↑v⁻¹ : ZMod n))
      val_inv := by ext <;> simp
      inv_val := by ext <;> simp }
  exact Units.map (ZMod.chineseRemainder hmn).symm.toMonoidHom uv

/-- A genuinely produced fresh prime realizes both prescribed residue
blocks beyond ANY bound. The proved Dirichlet theorem is applied only to
the actual CRT unit, so coprimality is not silently supplied. -/
theorem actual_fresh_prime (m n : ℕ) [NeZero m] [NeZero n]
    (hmn : Nat.Coprime m n) (u : (ZMod m)ˣ) (v : (ZMod n)ˣ) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ (p : ZMod m)=u ∧ (p : ZMod n)=v := by
  let w := mergedUnit m n hmn u v
  obtain ⟨p,hp,hprime,he⟩ := Nat.forall_exists_prime_gt_and_eq_mod w.isUnit N
  have hh := congrArg (ZMod.chineseRemainder hmn) he
  change (ZMod.chineseRemainder hmn) (p : ZMod (m*n)) =
    (ZMod.chineseRemainder hmn) ((ZMod.chineseRemainder hmn).symm
      ((u : ZMod m),(v : ZMod n))) at hh
  have hpair : ((p : ZMod m),(p : ZMod n))=((u : ZMod m),(v : ZMod n)) := by
    simpa only [map_natCast,RingEquiv.apply_symm_apply] using hh
  exact ⟨p,hp,hprime,congrArg Prod.fst hpair,congrArg Prod.snd hpair⟩

/-- Freshness with respect to an actual finite list of previously used
support primes is produced together with the two residue conditions. -/
theorem actual_fresh_prime_avoiding (m n : ℕ) [NeZero m] [NeZero n]
    (hmn : Nat.Coprime m n) (u : (ZMod m)ˣ) (v : (ZMod n)ˣ)
    (s : Finset ℕ) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p ∉ s ∧ (p : ZMod m)=u ∧ (p : ZMod n)=v := by
  obtain ⟨p,hp,hprime,hm,hn⟩ := actual_fresh_prime m n hmn u v (max N (s.sup id))
  refine ⟨p,lt_of_le_of_lt (le_max_left _ _) hp,hprime,?_,hm,hn⟩
  intro hs
  have hle : p ≤ s.sup id := Finset.le_sup (f:=id) hs
  exact (not_lt_of_ge (hle.trans (le_max_right _ _))) hp

/-- The retained auxiliary-prime types are literal unit classes modulo12.
Every already-prescribed unit residue modulo a coprime support modulus is
realized at a distinct fresh prime, with type1 or7 as required. -/
theorem actual_fresh_type_prime (m : ℕ) [NeZero m] (hm : Nat.Coprime m 12)
    (u : (ZMod m)ˣ) (s : Finset ℕ) (N : ℕ) (special : Bool) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p ∉ s ∧ (p : ZMod m)=u ∧
      (p : ZMod 12)=(if special then 7 else 1) := by
  let v : (ZMod 12)ˣ := if special then ZMod.unitOfCoprime 7 (by decide) else 1
  obtain ⟨p,hp,hprime,hs,hpu,hpv⟩ := actual_fresh_prime_avoiding m 12 hm u v s N
  refine ⟨p,hp,hprime,hs,hpu,?_⟩
  cases special <;> simpa [v] using hpv

end ActualTwoDescentFreshPrime318
