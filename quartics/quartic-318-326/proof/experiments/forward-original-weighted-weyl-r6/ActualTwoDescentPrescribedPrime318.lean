module
public import ActualTwoDescentResidueBits318
public section
noncomputable section
namespace ActualTwoDescentPrescribedPrime318
open ActualTwoDescentResidueBits318 ActualTwoDescentFreshPrime318 FixedSquarefreeCRT318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- One fresh auxiliary prime realizes EVERY prescribed symbol against
the already selected distinct support primes, plus the actual type1/7
modulo12, while avoiding the entire old support and a separate finite set.
Residue units, combined CRT class and prime are all PRODUCED here. -/
theorem actual_prescribed_prime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hcop : ∀ i, Nat.Coprime (p i) 12) (hp2 : ∀ i, p i ≠ 2)
    (bits : ι → Bool) (special : Bool) (forbidden : Finset ℕ) (N : ℕ) :
    ∃ q : ℕ, N < q ∧ q.Prime ∧ q ∉ forbidden ∧
      (∀ i, q ≠ p i) ∧ (q : ZMod 12)=(if special then 7 else 1) ∧
      ∀ i, quadraticChar (ZMod (p i)) (q : ZMod (p i))=bitSign (bits i) := by
  classical
  have hp : ∀ i, (p i).Prime := fun i => Fact.out
  choose u hu using (fun i => actual_bit_unit (p i) (hp2 i) (bits i))
  let U := supportUnit p hp hd u
  letI : NeZero (modulus p) := ⟨(modulus_positive p hp).ne'⟩
  have hM : Nat.Coprime (modulus p) 12 := by
    apply Nat.coprime_prod_left_iff.mpr
    intro i hi
    exact hcop i
  obtain ⟨q,hq,hprime,havoid,hqU,htype⟩ := actual_fresh_type_prime (modulus p) hM U
    (forbidden ∪ Finset.univ.image p) N special
  refine ⟨q,hq,hprime,fun hf => havoid (Finset.mem_union_left _ hf),?_,htype,?_⟩
  · intro i he
    apply havoid
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,he.symm⟩
  · intro i
    have hc := congrArg (component p i) hqU
    have hqi : (q : ZMod (p i))=(u i : ZMod (p i)) := by
      simpa only [map_natCast,U,actual_support_unit_component] using hc
    rw [hqi]
    exact hu i

end ActualTwoDescentPrescribedPrime318
