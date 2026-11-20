module
public import SelectedExceptionalDualEffectivity318
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public section
noncomputable section
open scoped BigOperators
open SelectedExceptionalDualEffectivity318

namespace SelectedCanonicalNefAdjunction318

/-- The only negative integral adjunction rate has arithmetic genus
zero and degree-one normalized negative self-intersection. -/
theorem negative_rate_iff (genus length : ℕ) (hLength : 0 < length) :
    (2*(genus:ℤ)+(length:ℤ)-2 < 0) ↔ genus = 0 ∧ length = 1 := by
  omega

/-- Here d is the positive residue-constants degree (with a common
positive arithmetic weight if used). Contraction of the exceptional
first-kind case is a geometric producer, not a hidden genus test. -/
theorem canonical_nonneg (genus length : ℕ) (hLength : 0 < length)
    (d self canonical : ℝ) (hd : 0 < d)
    (hself : self = -d*(length:ℝ))
    (adj : canonical + self = d*(2*(genus:ℝ)-2))
    (noFirstKind : ¬(genus = 0 ∧ length = 1)) :
    0 ≤ canonical := by
  have hrateZ : 0 ≤ 2*(genus:ℤ)+(length:ℤ)-2 :=
    le_of_not_gt fun hn => noFirstKind ((negative_rate_iff genus length hLength).mp hn)
  have hrate : 0 ≤ 2*(genus:ℝ)+(length:ℝ)-2 := by
    exact_mod_cast hrateZ
  have hrow : canonical = d*(2*(genus:ℝ)+(length:ℝ)-2) := by
    calc
      canonical = canonical + self - self := by ring
      _ = d*(2*(genus:ℝ)-2) - self := by rw [adj]
      _ = _ := by rw [hself]; ring
  rw [hrow]
  exact mul_nonneg hd.le hrate

/-- Replace the canonical-nef input of the exceptional order argument
by the actual normalized arithmetic adjunction rows and the absence
of a first-kind exceptional curve on the same resolution. -/
theorem exceptional_order_of_adjunction {ι : Type*} [Fintype ι]
    (Q : ι → ι → ℝ) (offDiag : ∀ i j, i ≠ j → 0 ≤ Q i j)
    (negative : ∀ v : ι → ℝ, v ≠ 0 → pairing Q v < 0)
    (ordM ordDJ rest K d : ι → ℝ) (genus length : ι → ℕ)
    (rest_nonneg : ∀ i, 0 ≤ rest i)
    (dPos : ∀ i, 0 < d i) (lengthPos : ∀ i, 0 < length i)
    (wDiag : ∀ i, Q i i = -d i*(length i:ℝ))
    (adj : ∀ i, K i + Q i i = d i*(2*(genus i:ℝ)-2))
    (noFirstKind : ∀ i, ¬(genus i = 0 ∧ length i = 1))
    (canonical_row : ∀ i,
      (∑ j, Q i j * (ordM j-ordDJ j)) + rest i = -K i) :
    ∀ i, ordDJ i ≤ ordM i :=
  exceptional_order_le Q offDiag negative ordM ordDJ rest K rest_nonneg
    (fun i => canonical_nonneg (genus i) (length i) (lengthPos i)
      (d i) (Q i i) (K i) (dPos i) (wDiag i) (adj i) (noFirstKind i))
    canonical_row

end SelectedCanonicalNefAdjunction318

#print axioms SelectedCanonicalNefAdjunction318.negative_rate_iff
#print axioms SelectedCanonicalNefAdjunction318.canonical_nonneg
#print axioms SelectedCanonicalNefAdjunction318.exceptional_order_of_adjunction
