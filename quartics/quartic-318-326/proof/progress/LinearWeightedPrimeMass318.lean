module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic
public section
noncomputable section

namespace LinearWeightedPrimeMass318
open scoped BigOperators

/-- Compare masses on *one and the same finite set of rational keys*. The
weight function is never divided by the number of Gaussian representatives. -/
def mass {α : Type*} (rows : Finset α) (w : α → ℝ) (P : α → Prop) : ℝ := by
  classical
  exact ∑ x ∈ rows, if P x then w x else 0

theorem mass_mono {α : Type*} (rows : Finset α) (w : α → ℝ)
    (P Q : α → Prop) (hn : ∀ x ∈ rows, 0 ≤ w x)
    (h : ∀ x ∈ rows, P x → Q x) : mass rows w P ≤ mass rows w Q := by
  classical
  unfold mass
  apply Finset.sum_le_sum
  intro x hx
  by_cases hp : P x
  · simp only [ite_eq_left hp, ite_eq_left (h x hx hp), le_refl]
  · by_cases hq : Q x
    · simpa only [ite_eq_right hp, ite_eq_left hq] using hn x hx
    · simp only [ite_eq_right hp, ite_eq_right hq, le_refl]

theorem survivor {α : Type*} (rows : Finset α) (w : α → ℝ)
    (safe bad : α → Prop) (hn : ∀ x ∈ rows, 0 ≤ w x)
    (h : mass rows w bad < mass rows w safe) :
    ∃ x ∈ rows, safe x ∧ ¬bad x := by
  by_contra! fail
  exact (not_le_of_gt h) (mass_mono rows w safe bad hn fail)

/-- Fixed-cutoff lower and upper mass estimates meet on a cofinal square
subsequence. The upper estimate may start at a cutoff-dependent threshold.
No estimate uniform in H and the cutoff jointly is assumed. -/
theorem square_cutoff_survivor {α : Type*}
    (rows : ℕ → Finset α) (weight : α → ℝ)
    (safe bad : ℕ → α → Prop)
    (hn : ∀ H x, x ∈ rows H → 0 ≤ weight x)
    (a c : ℝ) (_ha : 0 ≤ a) (hc : 0 < c) (n₀ H₀ : ℕ)
    (lower : ∀ n ≥ n₀, 0 < n → ∀ h₀ : ℕ, ∃ H ≥ h₀,
      c / (n:ℝ) * (H:ℝ)^4 ≤ mass (rows H) weight (safe (n^2)))
    (upper : ∀ n ≥ n₀, 0 < n → ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℕ, ∀ H ≥ h₀,
      mass (rows H) weight (bad (n^2)) ≤ (a / (n:ℝ)^2 + ε) * (H:ℝ)^4) :
    ∃ n ≥ n₀, ∃ H ≥ H₀, ∃ x ∈ rows H, safe (n^2) x ∧ ¬bad (n^2) x := by
  obtain ⟨k, hk⟩ := exists_nat_gt (a/c)
  let n := max (max n₀ 1) k
  have hn₀ : n₀ ≤ n := (le_max_left _ _).trans (le_max_left _ _)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans (le_max_left _ _)
  have hnpos : 0 < n := by omega
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hnpos
  have hk' : a < (k:ℝ)*c := (div_lt_iff₀ hc).mp hk
  have hkn : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast (le_max_right (max n₀ 1) k)
  have hgap : a/(n:ℝ)^2 < c/(n:ℝ) := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hnr) hnr).2
    have hanc : a < (n:ℝ)*c := hk'.trans_le (mul_le_mul_of_nonneg_right hkn hc.le)
    nlinarith [mul_lt_mul_of_pos_right hanc hnr]
  let ε := (c/(n:ℝ) - a/(n:ℝ)^2)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨h₁, hup⟩ := upper n hn₀ hnpos ε hε
  obtain ⟨H,hh,hlo⟩ := lower n hn₀ hnpos (max (max H₀ 1) h₁)
  have hb : h₁ ≤ H := (le_max_right _ _).trans hh
  have hH₀ : H₀ ≤ H := ((le_max_left _ _).trans (le_max_left _ _)).trans hh
  have hH1 : 1 ≤ H := ((le_max_right _ _).trans (le_max_left _ _)).trans hh
  have hHr : 0 < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hdiff : a/(n:ℝ)^2 + ε < c/(n:ℝ) := by dsimp [ε]; linarith
  have hstrict := (hup H hb).trans_lt (mul_lt_mul_of_pos_right hdiff (pow_pos hHr 4))
  obtain ⟨x,hx,hs,hd⟩ := survivor (rows H) weight _ _ (hn H) (hstrict.trans_le hlo)
  exact ⟨n,hn₀,H,hH₀,x,hx,hs,hd⟩

/-- The odd-prime obstruction is exactly the part of the mixed gcd not
already decided by the signed 2-adic ray. No exclusion of self-pairs. -/
theorem gcd_four (m n x y : ℕ) (hm : m = 4*x) (hn : n = 4*y)
    (hy : ¬2 ∣ y)
    (avoid : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬(p ∣ m ∧ p ∣ n)) :
    Nat.gcd m n = 4 := by
  have cop : Nat.gcd x y = 1 := by
    by_contra h
    obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd h
    have hx' := hd.trans (Nat.gcd_dvd_left x y)
    have hy' := hd.trans (Nat.gcd_dvd_right x y)
    have hp2 : p ≠ 2 := by rintro rfl; exact hy hy'
    exact avoid p hp hp2 ⟨hm ▸ dvd_mul_of_dvd_right hx' 4,
      hn ▸ dvd_mul_of_dvd_right hy' 4⟩
  rw [hm,hn,Nat.gcd_mul_left,cop,mul_one]

end LinearWeightedPrimeMass318
