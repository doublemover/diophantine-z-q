module

public import OriginalRCBooleanCubeDonor318
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Matching the zero address in the original terminal rank-one test

The dyadic coefficient rows are honest finite sign sums.  A single finite
binomial coefficient gives each row's equality indicator; no p-adic
exponent, Laurent series, or analytic input appears here.
-/

open scoped BigOperators

public section

noncomputable section

namespace OriginalRCTerminalAddress318

private abbrev Cube (b : ℕ) := Fin b → ZMod 2
private abbrev MP (b : ℕ) := MvPolynomial (Fin b) (ZMod 2)

private theorem bit_values (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private def bitSign (M : ℕ) (a : ZMod 2) : ZMod (2^M) :=
  if a = 0 then 1 else -1

private theorem bitSign_add (M : ℕ) (a d : ZMod 2) :
    bitSign M (a+d) = bitSign M a * bitSign M d := by
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  rcases bit_values a with rfl | rfl <;>
    rcases bit_values d with rfl | rfl <;> simp [bitSign, hone]

private theorem bitSign_val (M : ℕ) (a : ZMod 2) :
    bitSign M a = 1 - 2 * (a.val : ZMod (2^M)) := by
  have hone : (1 : ZMod 2).val = 1 := by decide
  rcases bit_values a with rfl | rfl
  · simp [bitSign]
  · simp only [bitSign, one_ne_zero, if_false, hone, Nat.cast_one]
    ring

/-- One literal sign-value row over the original terminal address cube. -/
@[expose] def signRow (M b : ℕ) (c : Finset (Fin b) → ZMod (2^M))
    (x : Fin b → ZMod 2) : ZMod (2^M) :=
  ∑ S : Finset (Fin b), c S * ∏ j ∈ S, (if x j = 0 then 1 else -1)

private theorem signRow_zero (M b : ℕ) (c : Finset (Fin b) → ZMod (2^M)) :
    signRow M b c 0 = ∑ S : Finset (Fin b), c S := by
  simp [signRow, Pi.zero_apply]

private def parityPoly {b : ℕ} (S : Finset (Fin b)) : MP b :=
  ∑ j ∈ S, MvPolynomial.X j

private theorem parityPoly_degree {b : ℕ} (S : Finset (Fin b)) :
    (parityPoly S).totalDegree ≤ 1 := by
  unfold parityPoly
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_X (R := ZMod 2) i).le

private theorem parityPoly_sign {b M : ℕ} (S : Finset (Fin b)) (x : Cube b) :
    bitSign M (MvPolynomial.eval x (parityPoly S)) =
      ∏ j ∈ S, (if x j = 0 then 1 else -1) := by
  classical
  simp only [parityPoly, map_sum, MvPolynomial.eval_X]
  induction S using Finset.induction_on with
  | empty => simp [bitSign]
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj, Finset.prod_insert hj, bitSign_add, ih] <;> rfl

private theorem last_cast (M : ℕ) :
    ((2^M-1 : ℕ) : ZMod (2^M)) = -1 := by
  have hp : 0 < (2:ℕ)^M := pow_pos (by decide) _
  have hs : (2:ℕ)^M-1+1 = (2:ℕ)^M := by omega
  have hz : (((2^M-1+1 : ℕ) : ZMod (2^M))) = 0 := by
    rw [hs, ZMod.natCast_self]
  rw [Nat.cast_add, Nat.cast_one] at hz
  calc
    ((2^M-1 : ℕ) : ZMod (2^M)) = (((2^M-1 : ℕ) : ZMod (2^M)) + 1) - 1 := by ring
    _ = -1 := by rw [hz, zero_sub]

private theorem one_add_X_pow_two_pow (M : ℕ) :
    (1 + Polynomial.X : Polynomial (ZMod 2))^((2:ℕ)^M) =
      1 + Polynomial.X^((2:ℕ)^M) := by
  have ht : (2 : Polynomial (ZMod 2)) = 0 := by
    calc
      (2 : Polynomial (ZMod 2)) = Polynomial.C (2 : ZMod 2) := by simp
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, map_zero]
  induction M with
  | zero => simp
  | succ M ih =>
      calc
        (1 + Polynomial.X : Polynomial (ZMod 2))^((2:ℕ)^(M+1)) =
            ((1 + Polynomial.X)^((2:ℕ)^M))^2 := by rw [← pow_mul, pow_succ (2:ℕ) M]
        _ = (1 + Polynomial.X^((2:ℕ)^M))^2 := by rw [ih]
        _ = 1 + (Polynomial.X^((2:ℕ)^M))^2 := by
          rw [add_sq, ht] <;> simp
        _ = 1 + Polynomial.X^((2:ℕ)^(M+1)) := by rw [pow_succ (2:ℕ) M, pow_mul]

private theorem coeff_mul_block (f : Polynomial (ZMod 2)) (p a k : ℕ) (hk : k < p) :
    (((1 + Polynomial.X^p)^a) * f).coeff k = f.coeff k := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [pow_succ', mul_assoc, add_mul, Polynomial.coeff_add, one_mul,
        Polynomial.coeff_X_pow_mul', if_neg (not_le.mpr hk), add_zero, ih]

/-- The last binomial coefficient below precision 2^M is the characteristic
function of exponent −1 modulo 2^M, including M=0. -/
theorem finite_binomial_indicator (M N : ℕ) :
    (((1 + Polynomial.X : Polynomial (ZMod 2))^N).coeff (2^M-1) = 1) ↔
      (N : ZMod (2^M)) = -1 := by
  have hp : 0 < (2:ℕ)^M := pow_pos (by decide) _
  have hL : (2:ℕ)^M-1 < (2:ℕ)^M := by omega
  have hr : N % (2:ℕ)^M < (2:ℕ)^M := Nat.mod_lt _ hp
  have hs :
      (1 + Polynomial.X : Polynomial (ZMod 2))^N =
        (1 + Polynomial.X^((2:ℕ)^M))^(N / (2:ℕ)^M) *
          (1 + Polynomial.X)^(N % (2:ℕ)^M) := by
    rw [← one_add_X_pow_two_pow, ← pow_mul, ← pow_add,
      add_comm ((2:ℕ)^M * (N / (2:ℕ)^M)), Nat.mod_add_div]
  rw [hs, coeff_mul_block _ _ _ _ hL, Polynomial.coeff_one_add_X_pow,
    ← last_cast M, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hL]
  by_cases h : N % (2:ℕ)^M = (2:ℕ)^M-1
  · simp [h, Nat.choose_self]
  · have hlt : N % (2:ℕ)^M < (2:ℕ)^M-1 := by omega
    simp [Nat.choose_eq_zero_of_lt hlt, h]

private def bounded {b : ℕ} (f : Polynomial (MP b)) : Prop :=
  ∀ k, (f.coeff k).totalDegree ≤ k

private theorem bounded_one (b : ℕ) : bounded (1 : Polynomial (MP b)) := by
  intro k
  rw [Polynomial.coeff_one]
  split <;> simp

private theorem bounded_add {b : ℕ} {f g : Polynomial (MP b)}
    (hf : bounded f) (hg : bounded g) : bounded (f+g) := by
  intro k
  rw [Polynomial.coeff_add]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hf k) (hg k))

private theorem bounded_mul {b : ℕ} {f g : Polynomial (MP b)}
    (hf : bounded f) (hg : bounded g) : bounded (f*g) := by
  intro k
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ab hab
  have hab' : ab.1 + ab.2 = k := Finset.mem_antidiagonal.mp hab
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (hab' ▸ Nat.add_le_add (hf ab.1) (hg ab.2))

private theorem bounded_pow {b : ℕ} {f : Polynomial (MP b)}
    (hf : bounded f) (a : ℕ) : bounded (f^a) := by
  induction a with
  | zero => simpa using bounded_one b
  | succ a ih => simpa only [pow_succ] using bounded_mul ih hf

private theorem bounded_prod {b : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (MP b)) (h : ∀ i ∈ s, bounded (f i)) :
    bounded (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_one b
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact bounded_mul (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem bounded_monomial {b : ℕ} (f : MP b) (n : ℕ)
    (hf : f.totalDegree ≤ n) : bounded (Polynomial.C f * Polynomial.X^n) := by
  intro k
  rw [Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · simpa [h] using hf
  · simp

private def multiplicity (M : ℕ) (c : ZMod (2^M)) : ℕ := (-c).val

private def generating (M b : ℕ) (c : Finset (Fin b) → ZMod (2^M)) :
    Polynomial (MP b) :=
  (1 + Polynomial.X)^(2^M-1) *
    ∏ S : Finset (Fin b),
      (1 + Polynomial.C (parityPoly S) * Polynomial.X^2)^(multiplicity M (c S))

private theorem generating_bounded (M b : ℕ) (c : Finset (Fin b) → ZMod (2^M)) :
    bounded (generating M b c) := by
  unfold generating
  apply bounded_mul
  · apply bounded_pow
    apply bounded_add (bounded_one b)
    simpa only [map_one, one_mul, pow_one] using
      (bounded_monomial (1 : MP b) 1 (by simp))
  · apply bounded_prod
    intro S _
    apply bounded_pow
    apply bounded_add (bounded_one b)
    exact bounded_monomial (parityPoly S) 2 ((parityPoly_degree S).trans (by decide))

private def exponent (M b : ℕ) (c : Finset (Fin b) → ZMod (2^M))
    (x : Cube b) : ℕ :=
  2^M-1 + ∑ S : Finset (Fin b),
    2 * multiplicity M (c S) * (MvPolynomial.eval x (parityPoly S)).val

private theorem eval_generating (M b : ℕ) (c : Finset (Fin b) → ZMod (2^M))
    (x : Cube b) :
    (generating M b c).map (MvPolynomial.eval x) =
      (1 + Polynomial.X : Polynomial (ZMod 2))^(exponent M b c x) := by
  unfold generating exponent
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_prod, Polynomial.map_C]
  rw [pow_add, ← Finset.prod_pow_eq_pow_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro S _
  rcases bit_values (MvPolynomial.eval x (parityPoly S)) with he | he
  · simp [he]
  · have hval : (1 : ZMod 2).val = 1 := by decide
    have hsq : (1 + Polynomial.X : Polynomial (ZMod 2))^2 = 1 + Polynomial.X^2 := by
      simpa only [pow_one] using one_add_X_pow_two_pow 1
    simp only [he, map_one, one_mul, hval, mul_one]
    rw [← hsq, ← pow_mul]

private theorem exponent_cast (M b : ℕ) (c : Finset (Fin b) → ZMod (2^M))
    (x : Cube b) :
    (exponent M b c x : ZMod (2^M)) = signRow M b c x - signRow M b c 0 - 1 := by
  have hp : (2:ℕ)^M ≠ 0 := pow_ne_zero _ (by decide)
  letI : NeZero ((2:ℕ)^M) := ⟨hp⟩
  rw [exponent, Nat.cast_add, last_cast, Nat.cast_sum, signRow_zero, signRow,
    ← Finset.sum_sub_distrib]
  calc
    (-1 : ZMod (2^M)) + (∑ S : Finset (Fin b),
        ((2 * multiplicity M (c S) * (MvPolynomial.eval x (parityPoly S)).val : ℕ) :
          ZMod (2^M))) =
      -1 + (∑ S : Finset (Fin b),
        (c S * ∏ j ∈ S, (if x j = 0 then 1 else -1)) - c S) := by
          congr 1
          apply Finset.sum_congr rfl
          intro S _
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_two, multiplicity, ZMod.natCast_zmod_val,
            ← parityPoly_sign, bitSign_val]
          ring
    _ = _ := by ring

private def indicator (M b : ℕ) (c : Finset (Fin b) → ZMod (2^M)) : MP b :=
  (generating M b c).coeff (2^M-1)

private theorem indicator_degree (M b : ℕ) (c : Finset (Fin b) → ZMod (2^M)) :
    (indicator M b c).totalDegree ≤ 2^M-1 :=
  generating_bounded M b c (2^M-1)

private theorem indicator_eval (M b : ℕ) (c : Finset (Fin b) → ZMod (2^M)) (x : Cube b) :
    MvPolynomial.eval x (indicator M b c) = 1 ↔ signRow M b c x = signRow M b c 0 := by
  rw [indicator, ← Polynomial.coeff_map, eval_generating,
    finite_binomial_indicator, exponent_cast]
  constructor <;> intro h
  · have h' : signRow M b c x - signRow M b c 0 = 0 := by
      calc
        signRow M b c x - signRow M b c 0 =
            (signRow M b c x - signRow M b c 0 - 1) + 1 := by ring
        _ = -1 + 1 := congrArg (fun y : ZMod (2^M) => y+1) h
        _ = 0 := by ring
    exact sub_eq_zero.mp h'
  · rw [h, sub_self, zero_sub]

/-- Under the literal budget of V13 (5.10), there is a nonzero address
agreeing with the zero address on every original dyadic sign test. -/
theorem exists_nonzero_matching_signRows (b M q : ℕ)
    (c : Fin q → Finset (Fin b) → ZMod (2^M))
    (h : q * (2^M-1) < b) :
    ∃ x : Fin b → ZMod 2, x ≠ 0 ∧
      ∀ i : Fin q, signRow M b (c i) x = signRow M b (c i) 0 := by
  classical
  let U : MP b := ∏ i : Fin q, indicator M b (c i)
  have hdegree : U.totalDegree < b := by
    apply lt_of_le_of_lt _ h
    calc
      U.totalDegree ≤ ∑ i : Fin q, (indicator M b (c i)).totalDegree :=
        MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ _i : Fin q, (2^M-1) := Finset.sum_le_sum fun i _ => indicator_degree M b (c i)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum := ZInQ.BooleanCube.sum_eval_eq_zero_of_totalDegree_lt b U hdegree
  have hzero : MvPolynomial.eval (0 : Cube b) U = 1 := by
    rw [U, map_prod]
    exact Finset.prod_eq_one fun i _ => (indicator_eval M b (c i) 0).mpr rfl
  by_contra hnone
  have hother (x : Cube b) (hx : x ≠ 0) : MvPolynomial.eval x U = 0 := by
    have hmiss : ∃ i : Fin q, signRow M b (c i) x ≠ signRow M b (c i) 0 := by
      by_contra hmiss
      apply hnone
      refine ⟨x, hx, ?_⟩
      intro i
      by_contra hi
      exact hmiss ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hmiss
    rw [U, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact (bit_values _).resolve_right fun he => hi ((indicator_eval M b (c i) x).mp he)
  have habs : (∑ x : Cube b, MvPolynomial.eval x U) = 1 := by
    rw [Finset.sum_eq_single (0 : Cube b)]
    · exact hzero
    · intro x _ hx
      exact hother x hx
    · simp
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0) (habs.symm.trans hsum)

end OriginalRCTerminalAddress318
