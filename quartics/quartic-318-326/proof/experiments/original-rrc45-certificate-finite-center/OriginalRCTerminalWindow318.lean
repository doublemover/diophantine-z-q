module

public import Mathlib.NumberTheory.Padics.RingHoms
import Lean.Elab.Tactic.Omega

/-!
# Finite scaled constant-term loss in the original rank-one argument

Only the finite constant-term rows enter here.  This module does not provide
those rows from Laurent series or construct a matching address.
-/

open scoped BigOperators

public section

noncomputable section

namespace OriginalRCTerminalWindow318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Coefficient residues at one dyadic precision (including precision zero). -/
abbrev Residue (M : ℕ) := ZMod (2^M)

/-- The canonical residue map after losing c bits of precision. -/
@[expose] def reduce (M c : ℕ) : Residue M →+* Residue (M-c) :=
  ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le M c)) _

/-- Cancellation of a power of two loses precision, rather than inverting
two in a finite coefficient ring.  In particular c=M is allowed. -/
theorem cancel_power {M c : ℕ} (hc : c ≤ M) (a : Residue M)
    (ha : (2 : Residue M)^c * a = 0) : reduce M c a = 0 := by
  letI : NeZero ((2:ℕ)^M) := ⟨pow_ne_zero _ (by decide)⟩
  have hlift : (a.val : Residue M) = a := ZMod.natCast_zmod_val a
  have hbig : (2:ℕ)^M ∣ (2:ℕ)^c * a.val := by
    apply (ZMod.natCast_eq_zero_iff ((2:ℕ)^c * a.val) ((2:ℕ)^M)).mp
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_two, hlift, ha]
  have hsum : c + (M-c) = M := by omega
  have hpow : (2:ℕ)^M = (2:ℕ)^c * (2:ℕ)^(M-c) := by rw [← pow_add, hsum]
  rw [hpow] at hbig
  have hsmall : (2:ℕ)^(M-c) ∣ a.val :=
    (mul_dvd_mul_iff_left (pow_ne_zero c (by decide : (2:ℕ) ≠ 0))).mp hbig
  rw [← hlift, map_natCast]
  exact (ZMod.natCast_eq_zero_iff a.val ((2:ℕ)^(M-c))).mpr hsmall

/-- Two actual constant-term rows already reduced modulo 2^M.  The indices of
negativeF and positiveU are paired: the jth element of Fin L means −(j+1)
for f and +(j+1) for the scaled u.  uZero and uOther are u(0) times 2^c,
whereas dZero and dOther are the original unscaled numerator constants. -/
structure ScaledWindow (M c L : ℕ) where
  unit : (Residue M)ˣ
  fZero : Residue M
  fOther : Residue M
  dZero : Residue M
  dOther : Residue M
  uZero : Residue M
  uOther : Residue M
  negativeF : Fin L → Residue M
  positiveU : Fin L → Residue M
  base_factor : fZero = (2 : Residue M)^c * (unit : Residue M)
  matching_f : fOther = fZero
  matching_d : dOther = dZero
  killed_tail : ∀ j, negativeF j = 0
  base_row : (2 : Residue M)^c * dZero = fZero * uZero
  other_row : (2 : Residue M)^c * dOther =
    fOther * uOther + ∑ j : Fin L, negativeF j * positiveU j

/-- This is the finite part of (5.11), before interpreting the scaled
coefficients as reductions of actual 2-adic integers. -/
theorem scaled_window_cancel {M c L : ℕ} (hc : c ≤ M) (W : ScaledWindow M c L) :
    reduce M c W.uOther = reduce M c W.uZero := by
  have hx : (2 : Residue M)^c * W.dOther = W.fOther * W.uOther := by
    simpa only [W.killed_tail, zero_mul, Finset.sum_const_zero, add_zero] using W.other_row
  have hprod : W.fZero * W.uOther = W.fZero * W.uZero := by
    calc
      W.fZero * W.uOther = W.fOther * W.uOther := by rw [W.matching_f]
      _ = (2 : Residue M)^c * W.dOther := hx.symm
      _ = (2 : Residue M)^c * W.dZero := by rw [W.matching_d]
      _ = W.fZero * W.uZero := W.base_row
  have hprod_zero : W.fZero * (W.uOther - W.uZero) = 0 := by
    rw [mul_sub, hprod, sub_self]
  have hunit_zero : (W.unit : Residue M) *
      ((2 : Residue M)^c * (W.uOther - W.uZero)) = 0 := by
    rw [← mul_assoc, mul_comm (W.unit : Residue M) ((2 : Residue M)^c),
      ← W.base_factor]
    exact hprod_zero
  have hcancel : (2 : Residue M)^c * (W.uOther - W.uZero) = 0 := by
    have h := congrArg (fun y : Residue M => (↑(W.unit⁻¹) : Residue M) * y) hunit_zero
    simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] using h
  have hz := cancel_power hc _ hcancel
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

private theorem lower_precision (M c : ℕ) (z : ℤ_[2]) :
    reduce M c (PadicInt.toZModPow M z) = PadicInt.toZModPow (M-c) z := by
  rw [reduce, ZMod.castHom_apply]
  exact PadicInt.cast_toZModPow (M-c) M (Nat.sub_le M c) z

/-- Recover the actual unscaled central difference from its scaled
integral lifts.  The result is zero or has nonnegative, natural-number
valuation at least M−2c.  No integer approximation is substituted for
the two 2-adic inputs. -/
theorem central_double_loss {M c L : ℕ} (hM : 2*c ≤ M)
    (W : ScaledWindow M c L) (UZero UOther : ℤ_[2])
    (hZero : PadicInt.toZModPow M UZero = W.uZero)
    (hOther : PadicInt.toZModPow M UOther = W.uOther) :
    ∃ δ : ℤ_[2], UOther - UZero = (2 : ℤ_[2])^c * δ ∧
      (δ = 0 ∨ M-2*c ≤ δ.valuation) := by
  have hc : c ≤ M := by omega
  have he : PadicInt.toZModPow (M-c) UOther =
      PadicInt.toZModPow (M-c) UZero := by
    simpa only [← hOther, ← hZero, lower_precision] using scaled_window_cancel hc W
  have hz : PadicInt.toZModPow (M-c) (UOther-UZero) = 0 := by
    rw [map_sub, he, sub_self]
  have hm : UOther-UZero ∈ RingHom.ker (PadicInt.toZModPow (p := 2) (M-c)) :=
    RingHom.mem_ker.mpr hz
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hm
  obtain ⟨z, hz'⟩ := hm
  have hsum : c + (M-2*c) = M-c := by omega
  refine ⟨(2 : ℤ_[2])^(M-2*c)*z, ?_, ?_⟩
  · rw [← mul_assoc, ← pow_add, hsum]
    exact hz'
  · by_cases h : (2 : ℤ_[2])^(M-2*c)*z = 0
    · exact Or.inl h
    · apply Or.inr
      apply (PadicInt.mem_span_pow_iff_le_valuation _ h (M-2*c)).mp
      exact Ideal.mem_span_singleton.mpr ⟨z, rfl⟩

/-- The strict budget in (5.11). If the base central value is zero and a
nonzero-address bound is B, the nonzero alternative contradicts that bound.
The zero alternative is itself incompatible with a nonzero-address value.
No positivity of the actual base valuation is required. -/
theorem central_strict_loss {M c L B : ℕ} (hM : B+2*c < M)
    (W : ScaledWindow M c L) (UZero UOther : ℤ_[2])
    (hZero : PadicInt.toZModPow M UZero = W.uZero)
    (hOther : PadicInt.toZModPow M UOther = W.uOther) :
    ∃ δ : ℤ_[2], UOther - UZero = (2 : ℤ_[2])^c * δ ∧
      (δ = 0 ∨ B < δ.valuation) := by
  obtain ⟨δ, hδ, hval⟩ :=
    central_double_loss (by omega : 2*c ≤ M) W UZero UOther hZero hOther
  rcases hval with hzero | hval
  · exact ⟨δ, hδ, Or.inl hzero⟩
  · exact ⟨δ, hδ, Or.inr (by omega)⟩

/-- Exact (5.11) value bound at supplied actual central values.  The only
additional hypotheses identify the paid integral lifts with the scaled
central values; there is no evaluation map on the Laurent ring here. -/
theorem central_value_double_loss {M c L : ℕ} (hM : 2*c ≤ M)
    (W : ScaledWindow M c L) (UZero UOther : ℤ_[2])
    (hZero : PadicInt.toZModPow M UZero = W.uZero)
    (hOther : PadicInt.toZModPow M UOther = W.uOther)
    (uZero uOther : ℚ_[2])
    (hz : (UZero : ℚ_[2]) = (2 : ℚ_[2])^c * uZero)
    (hx : (UOther : ℚ_[2]) = (2 : ℚ_[2])^c * uOther) :
    uOther-uZero = 0 ∨ ((M-2*c : ℕ) : ℤ) ≤ (uOther-uZero).valuation := by
  obtain ⟨δ, hδ, hval⟩ := central_double_loss hM W UZero UOther hZero hOther
  have hc2 : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := PadicInt.coe_natCast 2
  have hpow : (2 : ℚ_[2])^c ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (by decide : (2:ℕ) ≠ 0))
  have hq :
      (2 : ℚ_[2])^c * (uOther-uZero) = (2 : ℚ_[2])^c * (δ : ℚ_[2]) := by
    have hh := congrArg (fun q : ℤ_[2] => (q : ℚ_[2])) hδ
    simpa only [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow, hc2, hx, hz,
      ← mul_sub] using hh
  have hdiff : uOther-uZero = (δ : ℚ_[2]) := mul_left_cancel₀ hpow hq
  rcases hval with hval | hval
  · left
    rw [hdiff, hval, PadicInt.coe_zero]
  · right
    rw [hdiff, PadicInt.valuation_coe]
    omega

end OriginalRCTerminalWindow318
