module
public import ContactRadical318
public section
namespace ContactPrimeLimits318
open ContactRadical318 FiniteContact318
set_option maxHeartbeats 0

 theorem bad_prime (q:ℕ) (hq:q∈badPrimes) : q.Prime := by
  simp only [badPrimes,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

 theorem good_ge_nineteen (p:ℕ) (hp:p.Prime) (hg:p∉badPrimes) : 19≤p := by
  by_contra h
  have hlt:p<19:=by omega
  interval_cases p <;> norm_num [badPrimes] at *

 theorem good_not_dvd (p q:ℕ) (hp:p.Prime) (hg:p∉badPrimes) (hq:q∈badPrimes) : ¬p∣q := by
  intro hd
  have he: p=q := (Nat.prime_dvd_prime_iff_eq hp (bad_prime q hq)).mp hd
  exact hg (he ▸ hq)

 theorem good_exclusions (p:ℕ) (hp:p.Prime) (hg:p∉badPrimes) :
    19≤p ∧ ¬p∣contactModulus ∧ ¬p∣17 ∧ ¬p∣41 := by
  refine ⟨good_ge_nineteen p hp hg,?_,good_not_dvd p 17 hp hg (by simp [badPrimes]),good_not_dvd p 41 hp hg (by simp [badPrimes])⟩
  have h2:=good_not_dvd p 2 hp hg (by simp [badPrimes])
  have h3:=good_not_dvd p 3 hp hg (by simp [badPrimes])
  have h5:=good_not_dvd p 5 hp hg (by simp [badPrimes])
  have h7:=good_not_dvd p 7 hp hg (by simp [badPrimes])
  have h11:=good_not_dvd p 11 hp hg (by simp [badPrimes])
  have h37:=good_not_dvd p 37 hp hg (by simp [badPrimes])
  have h109:=good_not_dvd p 109 hp hg (by simp [badPrimes])
  have h439:=good_not_dvd p 439 hp hg (by simp [badPrimes])
  have h2399:=good_not_dvd p 2399 hp hg (by simp [badPrimes])
  simpa only [contactModulus,hp.dvd_mul,h2,h3,h5,h7,h11,h37,h109,h439,h2399,or_self,not_false_eq_true]

end ContactPrimeLimits318
#print axioms ContactPrimeLimits318.good_exclusions
