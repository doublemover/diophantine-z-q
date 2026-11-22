module
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Tactic
public section
noncomputable section

namespace LinearSelbergOmittedPrime318
open scoped BigOperators

def permitted (z : ℕ) (ok : ℕ → Prop) [DecidablePred ok] : Finset ℕ :=
  (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ ok d)

def weightSum (S : Finset ℕ) (w : ℕ → ℝ) : ℝ := ∑ d ∈ S, w d

/-- Prime removal for the actual truncated squarefree divisor sum, not an
Euler-product truncation at a smaller cutoff. Each removed multiple p·e
is charged exactly once to a retained term e at its original weight. -/
theorem omit_one (z p : ℕ) (hp : p.Prime)
    (ok : ℕ → Prop) [DecidablePred ok]
    (down : ∀ {a b : ℕ}, a∣b → ok b → ok a)
    (w : ℕ → ℝ) (hn : ∀ d, 0 ≤ w d)
    (mult : ∀ d, ¬p∣d → w (p*d)=w p*w d) :
    weightSum (permitted z ok) w ≤
      (1+w p)*weightSum ((permitted z ok).filter (fun d => ¬p∣d)) w := by
  classical
  let all := permitted z ok
  let keep := all.filter (fun d => ¬p∣d)
  let drop := all.filter (fun d => p∣d)
  let im := drop.image (fun d => d/p)
  have pair (d : ℕ) (hd : d∈drop) : p*(d/p)=d := by
    obtain ⟨e,he⟩ := (Finset.mem_filter.mp hd).2
    rw [he,Nat.mul_div_cancel_left e hp.pos]
  have inject : Set.InjOn (fun d : ℕ => d/p) (↑drop : Set ℕ) := by
    intro d hd e he h
    exact (pair d hd).symm.trans ((congrArg (fun n : ℕ => p*n) h).trans (pair e he))
  have reduced (d : ℕ) (hd : d∈drop) : d/p ∈ keep := by
    obtain ⟨hx,_⟩ := Finset.mem_filter.mp hd
    obtain ⟨hbox,hsq,hok⟩ := Finset.mem_filter.mp hx
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_Icc.mp hbox
    have edvd : d/p∣d := ⟨p,(pair d hd).symm.trans (Nat.mul_comm _ _)⟩
    have e₁ : 1≤d/p := by
      have nez : d/p≠0 := by
        intro e
        have h := pair d hd
        rw [e,mul_zero] at h
        omega
      exact Nat.one_le_iff_ne_zero.mpr nez
    have e₂ : d/p≤z := (Nat.div_le_self _ _).trans hp₂
    have sq : Squarefree (d/p) := by
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro ℓ hℓ hdvd
      exact Nat.squarefree_iff_prime_squarefree.mp hsq ℓ hℓ (hdvd.trans edvd)
    have no : ¬p∣d/p := by
      intro hdvd
      have H := Nat.mul_dvd_mul (dvd_refl p) hdvd
      rw [pair d hd] at H
      exact Nat.squarefree_iff_prime_squarefree.mp hsq p hp H
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨e₁,e₂⟩,sq,down edvd hok⟩,no⟩
  have sub : im ⊆ keep := by
    intro e he
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he
    exact reduced d hd
  have partition : weightSum all w = weightSum drop w + weightSum keep w := by
    exact (Finset.sum_filter_add_sum_filter_not all (fun d => p∣d) w).symm
  have exactDrop : weightSum drop w = w p * weightSum im w := by
    change (∑ d ∈ drop, w d) = w p*(∑ e ∈ drop.image (fun d => d/p), w e)
    rw [Finset.mul_sum,Finset.sum_image inject]
    apply Finset.sum_congr rfl
    intro d hd
    have H := mult (d/p) (Finset.mem_filter.mp (reduced d hd)).2
    rw [pair d hd] at H
    exact H
  have hsub : weightSum im w ≤ weightSum keep w :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (fun d _ _ => hn d)
  change weightSum all w ≤ (1+w p)*weightSum keep w
  rw [partition,exactDrop]
  calc
    _ ≤ w p*weightSum keep w + weightSum keep w :=
      add_le_add (mul_le_mul_of_nonneg_left hsub (hn p)) le_rfl
    _ = _ := by ring

/-- The ratio g/(1−g) ≤ 1 on every fresh prime where 0 ≤ g ≤ 1/2.
This is the fixed factor lost in the omitted-prime Selberg denominator. -/
theorem fresh_ratio (g : ℝ) (hg : 0 ≤ g) (hhalf : g ≤ 1/2) :
    0 ≤ g/(1-g) ∧ g/(1-g) ≤ 1 := by
  have h : 0<1-g := by linarith
  exact ⟨div_nonneg hg h.le,(div_le_iff₀ h).2 (by linarith)⟩

/-- A lower bound for one fixed-wheel truncated sum transfers uniformly
to the same sum with any one additional good prime omitted. -/
theorem uniform_lower (z p : ℕ) (hp : p.Prime)
    (ok : ℕ → Prop) [DecidablePred ok]
    (down : ∀ {a b : ℕ}, a∣b → ok b → ok a)
    (w : ℕ → ℝ) (hn : ∀ d, 0 ≤ w d) (hle : w p ≤ 1)
    (mult : ∀ d, ¬p∣d → w (p*d)=w p*w d)
    (L : ℝ) (low : L ≤ weightSum (permitted z ok) w) :
    L/2 ≤ weightSum ((permitted z ok).filter (fun d => ¬p∣d)) w := by
  have h := low.trans (omit_one z p hp ok down w hn mult)
  have hnkeep : 0 ≤ weightSum ((permitted z ok).filter (fun d => ¬p∣d)) w :=
    Finset.sum_nonneg (fun j _ => hn j)
  have h' := h.trans (mul_le_mul_of_nonneg_right (show 1+w p≤2 by linarith) hnkeep)
  linarith

/-- Multiplicative squarefree weight used by Selberg: the product of the
literal local ratios, not an independently assumed multiplicative function. -/
def localWeight (g : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∏ ℓ ∈ d.primeFactors, g ℓ/(1-g ℓ)

theorem localWeight_prime (g : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    localWeight g p = g p/(1-g p) := by
  simp only [localWeight,hp.primeFactors,Finset.prod_singleton]

theorem localWeight_mult (g : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (d : ℕ) (hd : ¬p∣d) :
    localWeight g (p*d) = localWeight g p * localWeight g d := by
  have hc := hp.coprime_iff_not_dvd.mpr hd
  unfold localWeight
  rw [hc.primeFactors_mul,Finset.prod_union hc.disjoint_primeFactors]

def outside (wheel : Finset ℕ) (d : ℕ) : Prop := ∀ p ∈ wheel, ¬p∣d

theorem outside_down (wheel : Finset ℕ) {a b : ℕ} (d : a∣b) (h : outside wheel b) :
    outside wheel a := by
  intro p hp ha
  exact h p hp (ha.trans d)

open Classical in
/-- Actual local weights and the fixed finite wheel, with a single further
prime omitted. The unomitted analytic growth estimate is the only lower
bound still needed here. -/
theorem wheel_uniform_lower (z p : ℕ) (hp : p.Prime) (wheel : Finset ℕ) (g : ℕ → ℝ)
    (good : ∀ ℓ : ℕ, 0≤g ℓ ∧ g ℓ≤1/2)
    (L : ℝ) (hL : L ≤ weightSum (permitted z (outside wheel)) (localWeight g)) :
    L/2 ≤ weightSum ((permitted z (outside wheel)).filter (fun d => ¬p∣d)) (localWeight g) := by
  have hn (d : ℕ) : 0 ≤ localWeight g d :=
    Finset.prod_nonneg (fun ℓ _ => (fresh_ratio (g ℓ) (good ℓ).1 (good ℓ).2).1)
  have hle : localWeight g p≤1 := by
    rw [localWeight_prime g hp]
    exact (fresh_ratio (g p) (good p).1 (good p).2).2
  exact uniform_lower z p hp (outside wheel) (outside_down wheel)
    (localWeight g) hn hle (fun d hd => localWeight_mult g hp d hd) L hL

end LinearSelbergOmittedPrime318
