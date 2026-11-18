module
public import GeneralScalarDepth318
public section
noncomputable section
namespace RationalScalarSupport318
set_option maxHeartbeats 1000000

/-- Exact positive-valuation support, enlarged by the three distinguished
primes so all later unit/depth consumers share one nonempty finite family. -/
@[expose] def support (q : ℚ) : Finset ℕ :=
  insert 2 (insert 3 (insert 17 q.num.natAbs.primeFactors))

lemma mem_prime (q : ℚ) (p : ℕ) (hp : p∈support q) : p.Prime := by
  simp only [support,Finset.mem_insert] at hp
  rcases hp with rfl|rfl|rfl|hp
  · norm_num
  · norm_num
  · norm_num
  · exact (Nat.mem_primeFactors.mp hp).1

lemma positive_mem (q : ℚ) (hq : q≠0) (p : ℕ) (hp : p.Prime)
    (hv : 0<padicValRat p q) : p∈support q := by
  have hn : q.num.natAbs≠0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq)
  have hval : padicValNat p q.num.natAbs≠0 := by
    intro he
    rw [padicValRat_def,padicValInt,he] at hv
    omega
  have hd : p∣q.num.natAbs := padicValNat.dvd_of_ne_zero hval
  have hm := Nat.mem_primeFactors.mpr ⟨hp,hd,hn⟩
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))

@[expose] abbrev Index (q : ℚ) := {p : ℕ // p∈support q}
instance index_prime (q : ℚ) (p : Index q) : Fact p.val.Prime := ⟨mem_prime q p.val p.2⟩

lemma two_mem (q : ℚ) : 2∈support q := Finset.mem_insert_self _ _
lemma three_mem (q : ℚ) : 3∈support q := by simp [support]
lemma seventeen_mem (q : ℚ) : 17∈support q := by simp [support]

end RationalScalarSupport318
