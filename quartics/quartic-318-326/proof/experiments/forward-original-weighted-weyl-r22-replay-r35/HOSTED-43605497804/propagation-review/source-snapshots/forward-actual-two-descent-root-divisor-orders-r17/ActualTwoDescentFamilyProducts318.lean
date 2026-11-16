module
public import ActualTwoDescentPrimeFamily318
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Algebra.BigOperators.Fin
public section
noncomputable section
namespace ActualTwoDescentFamilyProducts318
open ActualTwoDescentPrimeFamily318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {ι : Type*} {p : ι → ℕ} {oldBits : ℕ → ι → Bool}
  {newBits : ℕ → ℕ → Bool} {special : ℕ → Bool} {forbidden : Finset ℕ} {N k : ℕ}

/-- The auxiliary squarefree multiplier consists of the produced primes
with their original indexing, including the distinguished last prime. -/
def multiplier (F : PrimeFamily p oldBits newBits special forbidden N k) : ℕ :=
  ∏ i, F.value i

lemma actual_multiplier_positive (F : PrimeFamily p oldBits newBits special forbidden N k) :
    0 < multiplier F := by
  apply Finset.prod_pos
  intro i _
  exact (F.prime i).pos

lemma actual_multiplier_squarefree (F : PrimeFamily p oldBits newBits special forbidden N k) :
    Squarefree (multiplier F) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    apply Nat.coprime_iff_isRelPrime.mp
    apply (Nat.coprime_primes (F.prime i) (F.prime j)).mpr
    exact fun he => hij (F.injective he)
  · intro i _
    exact (F.prime i).squarefree

/-- Avoiding every prime in the original support excludes every shared
factor of the entire multiplier, not just equality with a chosen factor. -/
lemma actual_multiplier_coprime (F : PrimeFamily p oldBits newBits special forbidden N k)
    (m : ℕ) (cover : ∀ q : ℕ, q.Prime → q ∣ m → ∃ i, p i=q) :
    Nat.Coprime (multiplier F) m := by
  apply Nat.coprime_prod_left_iff.mpr
  intro i _
  apply (F.prime i).coprime_iff_not_dvd.mpr
  intro hdiv
  obtain ⟨j,hj⟩ := cover (F.value i) (F.prime i) hdiv
  exact F.seed_ne i j hj.symm

/-- Exactly one type7 prime and all other type1 primes give multiplier7
modulo12, for every family size including no nondistinguished auxiliaries. -/
lemma actual_multiplier_residue (d : ℕ)
    (F : PrimeFamily p oldBits newBits (fun i => decide (i=d)) forbidden N (d+1)) :
    (multiplier F : ZMod 12)=7 := by
  have hlast : (F.value (Fin.last d) : ZMod 12)=7 := by
    simpa using F.residue (Fin.last d)
  have hprev : ∀ i : Fin d, (F.value i.castSucc : ZMod 12)=1 := by
    intro i
    have hi : i.val ≠ d := Nat.ne_of_lt i.isLt
    simpa [hi] using F.residue i.castSucc
  rw [multiplier, Nat.cast_prod, Fin.prod_univ_castSucc, hlast]
  have hp : (∏ i : Fin d, (F.value i.castSucc : ZMod 12))=1 := by
    apply Finset.prod_eq_one
    intro i _
    exact hprev i
  rw [hp, one_mul]

end ActualTwoDescentFamilyProducts318
