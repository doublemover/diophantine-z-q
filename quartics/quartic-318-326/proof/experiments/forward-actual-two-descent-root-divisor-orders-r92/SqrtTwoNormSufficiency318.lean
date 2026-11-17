module
public import SqrtTwoSplitPrime318
public import Mathlib.Data.Nat.Factorization.Basic
public section
noncomputable section
namespace SqrtTwoNormSufficiency318
open SqrtTwoSplitPrime318

private lemma norm_pow (g : K) (e : ℕ) :
    (g^e).norm.natAbs = g.norm.natAbs^e := by
  induction e with
  | zero => simp [Zsqrtd.norm_one]
  | succ e ih => simp only [pow_succ, Zsqrtd.norm_mul, Int.natAbs_mul, ih]

private lemma norm_prod {ι : Type*} (s : Finset ι) (g : ι → K) :
    (∏ i ∈ s, g i).norm.natAbs = ∏ i ∈ s, (g i).norm.natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Zsqrtd.norm_one]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Zsqrtd.norm_mul, Int.natAbs_mul, ih]

/-- A prime power has an integral absolute-norm witness when its exponent
is even or 2 has a modular square root. No residue-class classification of
primes and no global representation principle is assumed. -/
theorem prime_power (p e : ℕ) (hp : p.Prime)
    (h : Even e ∨ IsSquare (2 : ZMod p)) :
    ∃ g : K, g.norm.natAbs = p^e := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases h with ⟨k,rfl⟩ | ⟨a,ha⟩
  · refine ⟨(p^k : ℕ), ?_⟩
    rw [Zsqrtd.norm_natCast]
    simp [Int.natAbs_mul, pow_add]
  · obtain ⟨g,hg⟩ := SqrtTwoSplitPrime318.prime_norm p a
      (by simpa only [pow_two] using ha.symm)
    exact ⟨g^e, by rw [norm_pow, hg]⟩

/-- The sufficiency half of the integral absolute-norm criterion. Every
inert-prime exponent is assumed even, then actual prime witnesses are
constructed and multiplied. This does not choose the auxiliary binary
quadratic value needed by the anchor's local-global problem. -/
theorem natural_norm (n : ℕ) (hn : n≠0)
    (h : ∀ p : ℕ, p.Prime → ¬IsSquare (2 : ZMod p) → Even (n.factorization p)) :
    ∃ g : K, g.norm.natAbs=n := by
  classical
  have he : ∀ p : ℕ, ∃ g : K,
      p∈n.primeFactors → g.norm.natAbs=p^(n.factorization p) := by
    intro p
    by_cases hp : p∈n.primeFactors
    · have hprime := Nat.prime_of_mem_primeFactors hp
      have hc : Even (n.factorization p) ∨ IsSquare (2 : ZMod p) := by
        by_cases hs : IsSquare (2 : ZMod p)
        · exact Or.inr hs
        · exact Or.inl (h p hprime hs)
      obtain ⟨g,hg⟩ := prime_power p (n.factorization p) hprime hc
      exact ⟨g, fun _ => hg⟩
    · exact ⟨1, fun hm => (hp hm).elim⟩
  choose g hg using he
  refine ⟨∏ p ∈ n.primeFactors, g p, ?_⟩
  calc
    (∏ p ∈ n.primeFactors, g p).norm.natAbs
        = ∏ p ∈ n.primeFactors, (g p).norm.natAbs := norm_prod _ _
    _ = ∏ p ∈ n.primeFactors, p^(n.factorization p) :=
      Finset.prod_congr rfl (fun p hp => hg p hp)
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

end SqrtTwoNormSufficiency318
