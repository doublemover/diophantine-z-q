module
public import Mathlib.Tactic
public import Mathlib.Data.Nat.Prime.Basic
public section
noncomputable section
namespace ActualLinearQFiniteExclusion318
open scoped BigOperators
open Classical

/-- Directed incidence includes the diagonal. No independence of signs,
positions, or of the medium and large exceptional sets is used. -/
@[expose] def Hit {I J : Type*} (Nminus Nplus : I → J → ℕ) (x : I) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ ∃ s t, p ∣ Nminus x s ∧ p ∣ Nplus x t

@[expose] def Medium {I J : Type*} (Nminus Nplus : I → J → ℕ)
    (s Y : ℕ) (x : I) : Prop :=
  ∃ p, s < p ∧ p ≤ Y ∧ Hit Nminus Nplus x p

@[expose] def Large {I J : Type*} (Nminus Nplus : I → J → ℕ)
    (Y : ℕ) (x : I) : Prop :=
  ∃ p, Y < p ∧ Hit Nminus Nplus x p

@[expose] def mass {I : Type*} (S : Finset I) (w : I → ℝ) (P : I → Prop) : ℝ :=
  ∑ x ∈ S, @ite ℝ (P x) (Classical.propDecidable _) (w x) 0

/-- The same finite carrier and weight occur three times. Overlap in the two
bad events is permitted; deleting an event cannot increase its charge. -/
theorem survive {I J : Type*} (S : Finset I) (w : I → ℝ)
    (Nminus Nplus : I → J → ℕ) (s Y : ℕ)
    (hW : ∀ x ∈ S, 0 ≤ w x)
    (hSmall : ∀ x ∈ S, ∀ p ≤ s, ¬ Hit Nminus Nplus x p)
    (hMass : mass S w (Medium Nminus Nplus s Y) + mass S w (Large Nminus Nplus Y)
      < ∑ x ∈ S, w x) :
    ∃ x ∈ S, ∀ p, ¬ Hit Nminus Nplus x p := by
  classical
  by_contra H
  push_neg at H
  apply (not_le_of_gt hMass)
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨p,hp⟩ := H x hx
  have hs : s < p := lt_of_not_ge (fun h => hSmall x hx p h hp)
  by_cases hY : p ≤ Y
  · have ha : Medium Nminus Nplus s Y x := ⟨p,hs,hY,hp⟩
    by_cases hb : Large Nminus Nplus Y x
    · rw [if_pos ha,if_pos hb]
      linarith only [hW x hx]
    · rw [if_pos ha,if_neg hb,add_zero]
  · have hb : Large Nminus Nplus Y x := ⟨p,lt_of_not_ge hY,hp⟩
    by_cases ha : Medium Nminus Nplus s Y x
    · rw [if_pos ha,if_pos hb]
      linarith only [hW x hx]
    · rw [if_neg ha,if_pos hb,zero_add]

/-- The wheel cutoff is m². A lower A N²/m and medium D N²/m²+E with
E and the large term at most A N²/(4m) suffice once 4D < A m. -/
theorem strict_budget (A D m N E F total medium large : ℝ)
    (hA : 0 < A) (hm : 0 < m) (hN : 0 < N) (hgap : 4*D < A*m)
    (hE : E ≤ A*N^2/(4*m)) (hF : F ≤ A*N^2/(4*m))
    (hlow : A*N^2/m ≤ total) (hmedium : medium ≤ D*N^2/m^2+E) (hlarge : large ≤ F) :
    medium+large < total := by
  have hN2 : 0 < N^2 := by positivity
  have hm2 : 0 < m^2 := by positivity
  have h4m : 0 < 4*m := mul_pos (by norm_num) hm
  have htail : D*N^2/m^2 < A*N^2/(4*m) := by
    apply (div_lt_div_iff₀ hm2 h4m).2
    have h := mul_lt_mul_of_pos_right hgap (mul_pos hN2 hm)
    convert h using 1 <;> ring
  have hquarter : 0 < A*N^2/(4*m) := div_pos (mul_pos hA hN2) h4m
  have hscale : A*N^2/m = 4*(A*N^2/(4*m)) := by field_simp [hm.ne'] <;> ring
  linarith only [hE,hF,hlow,hmedium,hlarge,htail,hquarter,hscale]

/-- The plus quarter is odd. Absence of an odd incidence gives the
exact gcd-four on the original norms. -/
theorem gcd_four (nminus nplus l r : ℕ)
    (hl : nminus = 4*l) (hr : nplus = 4*r) (ho : Odd r)
    (h : ∀ p, p.Prime → p ≠ 2 → ¬ (p ∣ nminus ∧ p ∣ nplus)) :
    Nat.gcd nminus nplus = 4 := by
  have hc : Nat.Coprime l r := by
    apply Nat.coprime_of_dvd'
    intro p hp hpl hpr
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      obtain ⟨a,ha⟩ := ho
      obtain ⟨b,hb⟩ := hpr
      omega
    exact False.elim (h p hp hp2
      ⟨hpl.trans (by rw [hl]; exact dvd_mul_left l 4),
       hpr.trans (by rw [hr]; exact dvd_mul_left r 4)⟩)
  rw [hl,hr,Nat.gcd_mul_left]
  change Nat.gcd l r = 1 at hc
  rw [hc,mul_one]

end ActualLinearQFiniteExclusion318
