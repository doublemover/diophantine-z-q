module
public import ActualAffineChebClassUnion318
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public section
noncomputable section
namespace ActualChebVonMangoldt318
open scoped BigOperators
open ArithmeticFunction ActualAffineChebClassUnion318

variable {J : Type*} [DecidableEq J]

/-- Exactly the FT (1.9) convention: at p^e the tag is that of p,
NOT the Frobenius raised to e. The native arithmetic von Mangoldt
function supplies the weight and its proper-power support. -/
@[expose] def classMangoldt (tag : ℕ → Option J) (j : J) (n : ℕ) : ℝ :=
  part (tag n.minFac) (vonMangoldt n) j

theorem class_prime_power (tag : ℕ → Option J) (j : J) {p e : ℕ}
    (hp : p.Prime) (he : e ≠ 0) :
    classMangoldt tag j (p^e) = part (tag p) (Real.log p) j := by
  rw [classMangoldt,Nat.pow_minFac he, hp.minFac_eq,
    vonMangoldt_apply_pow he,vonMangoldt_apply_prime hp]

theorem class_prime (tag : ℕ → Option J) (j : J) {p : ℕ} (hp : p.Prime) :
    classMangoldt tag j p = part (tag p) (Real.log p) j := by
  rw [classMangoldt,hp.minFac_eq,vonMangoldt_apply_prime hp]

theorem class_nonnegative (tag : ℕ → Option J) (j : J) (n : ℕ) :
    0 ≤ classMangoldt tag j n := by
  unfold classMangoldt part
  split
  · exact vonMangoldt_nonneg
  · exact le_rfl

theorem class_at_most_log (tag : ℕ → Option J) (j : J) (n : ℕ) :
    classMangoldt tag j n ≤ Real.log (n:ℝ) := by
  have hlog : 0 ≤ Real.log (n:ℝ) :=
    vonMangoldt_nonneg.trans vonMangoldt_le_log
  unfold classMangoldt part
  split
  · exact vonMangoldt_le_log
  · exact hlog

theorem class_supported (tag : ℕ → Option J) (j : J) (n : ℕ) :
    classMangoldt tag j n ≠ 0 → IsPrimePow n := by
  intro h
  unfold classMangoldt part at h
  split at h
  · exact vonMangoldt_ne_zero_iff.mp h
  · exact False.elim (h rfl)

theorem union_weight [Fintype J] (tag : ℕ → Option J) (n : ℕ) :
    (∑ j : J, classMangoldt tag j n) =
      if (tag n.minFac).isSome then vonMangoldt n else 0 :=
  sum_parts (tag n.minFac) (vonMangoldt n)

end ActualChebVonMangoldt318
