module
public import Mathlib
public section
noncomputable section
namespace ActualFTTwoElementCoefficient318

open scoped BigOperators

variable {A R : Type*} [DecidableEq A] [Monoid R] [DecidableEq R]

/-- The normalized finite factor D⋅η of (1.10)/(1.15), not an assertion
that any primes are equidistributed. The norm is unit-valued and so
failure of coprimality gives zero without a separate CRT branch. -/
@[expose] def scaledEta (D G : ℕ) (norm : A → Rˣ) (C : Finset A) (b : R) : ℝ := by
  classical
  exact if IsUnit b ∧ (∀ a∈C,(norm a:R)=b) then
    ((D:ℝ)*(C.card:ℝ))/(G:ℝ) else 0

/-- A fixed representative yields one rational conjugacy class, not
one class for each of its two signs. -/
@[expose] def entry (D G : ℕ) (norm : A → Rˣ) (a : A) (b : R) : ℝ :=
  if (norm a:R)=b then (2*(D:ℝ))/(G:ℝ) else 0

theorem scaled_two (D G : ℕ) (norm : A → Rˣ) (a a' : A) (h : a≠a')
    (hn : norm a'=norm a) (b : R) :
    scaledEta D G norm {a,a'} b=entry D G norm a b := by
  classical
  have hc : ({a,a'}:Finset A).card=2 := Finset.card_pair h
  by_cases hb : (norm a:R)=b
  · have hu : IsUnit b := hb ▸ (norm a).isUnit
    have hCompat : ∀ z ∈ ({a,a'}:Finset A), (norm z:R)=b := by
      intro z hz
      rcases Finset.mem_insert.mp hz with hz|hz
      · rwa [hz]
      · rw [Finset.mem_singleton] at hz
        rw [hz,hn]
        exact hb
    rw [scaledEta,if_pos ⟨hu,hCompat⟩,entry,if_pos hb,hc]
    norm_num <;> ring
  · have hNo : ¬ (IsUnit b ∧ ∀ z ∈ ({a,a'}:Finset A),(norm z:R)=b) := by
      intro hB
      exact hb (hB.2 a (Finset.mem_insert_self _ _))
    rw [scaledEta,if_neg hNo,entry,if_neg hb]

/-- Exact finite class union at a fixed shared rational cell. Zero
entries are retained, including all incompatible classes of a slot. -/
theorem sum_entries {J : Type*} [Fintype J] (D G : ℕ) (norm : A → Rˣ)
    (pick : J → A) (b : R) :
    (∑ j : J,entry D G norm (pick j) b)=
      ((Finset.univ.filter (fun j : J => (norm (pick j):R)=b)).card:ℝ)*
        (2*(D:ℝ)/(G:ℝ)) := by
  classical
  simp only [entry,←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]

theorem entry_nonneg (D G : ℕ) (norm : A → Rˣ) (a : A) (b : R) :
    0≤entry D G norm a b := by
  unfold entry
  split <;> positivity

end ActualFTTwoElementCoefficient318
