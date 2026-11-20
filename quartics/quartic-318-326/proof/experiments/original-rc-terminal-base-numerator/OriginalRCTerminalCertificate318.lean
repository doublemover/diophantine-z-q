module

public import OriginalRCTerminalAddress318
public import OriginalRCTerminalWindow318
import Lean.Elab.Tactic.Omega

/-!
# From actual bounded terminal rows to a nonzero base central value

Only supplied finite coefficient rows are used.  In particular, integral
scaling at another address is requested after the matching tests, not at all
addresses.  The theorem has no Heegner, rank, or Laurent production input.
-/

open scoped BigOperators

public section

noncomputable section

namespace OriginalRCTerminalCertificate318

open OriginalRCTerminalAddress318 OriginalRCTerminalWindow318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The retained determinant precision budget in (5.9). -/
@[expose] def detBudget (a hK cE tK : ℕ) : ℕ := a+4*(hK+2*cE+2*tK)

/-- The number of negative coefficient tests in (5.9). -/
@[expose] def poleCutoff (dK M : ℕ) : ℕ := 16*(dK+5)*M

/-- Test slot of the coefficient of f at −(j+1). -/
@[expose] def negativeSlot {L : ℕ} (j : Fin L) : Fin (L+2) :=
  ⟨j.val, by have h := j.isLt; omega⟩

/-- Test slot of the constant coefficient of f. -/
@[expose] def constantFSlot (L : ℕ) : Fin (L+2) := ⟨L, by omega⟩

/-- Test slot of the constant coefficient of d. -/
@[expose] def constantDSlot (L : ℕ) : Fin (L+2) := ⟨L+1, by omega⟩

/-- Honest simultaneous sign tests for precisely the original coefficient
slots: L negative coefficients of f, its constant, and the constant of d. -/
abbrev Tests (b M L : ℕ) := Fin (L+2) → Finset (Fin b) → Residue M

@[expose] def testValue {b M L : ℕ} (T : Tests b M L)
    (i : Fin (L+2)) (x : Fin b → ZMod 2) : Residue M :=
  signRow M b (T i) x

/-- The actual central data and normalized finite coefficient equations.
The positive array pairs coefficient +(j+1) of the scaled series with the
negative f coefficient at −(j+1).  The caller supplies proof that this
is the complete finite constant-term equation, with no omitted tail. -/
structure Certificate (b M c L : ℕ) where
  tests : Tests b M L
  central : (Fin b → ZMod 2) → ℚ_[2]
  unit : (Residue M)ˣ
  baseLift : ℤ_[2]
  baseScaled : (baseLift : ℚ_[2]) = (2 : ℚ_[2])^c * central 0
  baseFactor : testValue tests (constantFSlot L) 0 = (2 : Residue M)^c * ↑unit
  baseNegative : ∀ j : Fin L, testValue tests (negativeSlot j) 0 = 0
  baseRow : (2 : Residue M)^c * testValue tests (constantDSlot L) 0 =
    testValue tests (constantFSlot L) 0 * PadicInt.toZModPow M baseLift
  otherLift : ∀ x : Fin b → ZMod 2, x ≠ 0 →
    (∀ i, testValue tests i x = testValue tests i 0) →
    ∃ (U : ℤ_[2]) (positiveU : Fin L → Residue M),
      (U : ℚ_[2]) = (2 : ℚ_[2])^c * central x ∧
      (2 : Residue M)^c * testValue tests (constantDSlot L) x =
        testValue tests (constantFSlot L) x * PadicInt.toZModPow M U +
          ∑ j : Fin L, testValue tests (negativeSlot j) x * positiveU j

/-- The two finite producers give a nonzero address at the (5.10) budget
and exactly the original central comparison (5.11) at that address. -/
theorem exists_central_comparison {b M c L : ℕ} (P : Certificate b M c L)
    (hM : 2*c ≤ M) (hb : (L+2)*(2^M-1) < b) :
    ∃ x : Fin b → ZMod 2, x ≠ 0 ∧
      (P.central x - P.central 0 = 0 ∨
        ((M-2*c : ℕ) : ℤ) ≤ (P.central x - P.central 0).valuation) := by
  obtain ⟨x, hx, hm⟩ := exists_nonzero_matching_signRows b M (L+2) P.tests hb
  have hm' : ∀ i, testValue P.tests i x = testValue P.tests i 0 := hm
  obtain ⟨U, pos, uscale, hrow⟩ := P.otherLift x hx hm'
  let W : ScaledWindow M c L := {
    unit := P.unit
    fZero := testValue P.tests (constantFSlot L) 0
    fOther := testValue P.tests (constantFSlot L) x
    dZero := testValue P.tests (constantDSlot L) 0
    dOther := testValue P.tests (constantDSlot L) x
    uZero := PadicInt.toZModPow M P.baseLift
    uOther := PadicInt.toZModPow M U
    negativeF := fun j => testValue P.tests (negativeSlot j) x
    positiveU := pos
    base_factor := P.baseFactor
    matching_f := hm' (constantFSlot L)
    matching_d := hm' (constantDSlot L)
    killed_tail := fun j => (hm' (negativeSlot j)).trans (P.baseNegative j)
    base_row := P.baseRow
    other_row := hrow }
  exact ⟨x, hx, central_value_double_loss hM W P.baseLift U rfl rfl
    (P.central 0) (P.central x) P.baseScaled uscale⟩

/-- Terminal arithmetic contradiction against a given upper bound at every
nonzero address.  The nonzero hypothesis is necessary because Mathlib's field
valuation assigns the representative value 0 at the zero element. -/
theorem central_base_ne_zero {b M c L B : ℕ} (P : Certificate b M c L)
    (hM : B+2*c < M) (hb : (L+2)*(2^M-1) < b)
    (hupper : ∀ x, x ≠ 0 → P.central x ≠ 0 ∧ (P.central x).valuation ≤ (B:ℤ)) :
    P.central 0 ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hcmp⟩ := exists_central_comparison P (by omega : 2*c ≤ M) hb
  have hxupper := hupper x hx
  rw [h0, sub_zero] at hcmp
  rcases hcmp with hzero | hlower
  · exact hxupper.1 hzero
  · have hbits : B < M-2*c := by omega
    have hu := hxupper.2
    omega

/-- Literal V13 constants and strict inequalities with natural nonnegative
precision data. The selected address is produced inside the argument, not
given as an additional premise. No claim that a certificate exists. -/
theorem central_base_ne_zero_of_original_bounds
    (a hK cE tK dK b M c B : ℕ)
    (P : Certificate b M c (poleCutoff dK M))
    (hc : c ≤ detBudget a hK cE tK)
    (hM : max (detBudget a hK cE tK) (max (B+2*detBudget a hK cE tK) 0) < M)
    (hb : (poleCutoff dK M+2)*(2^M-1) < b)
    (hupper : ∀ x, x ≠ 0 → P.central x ≠ 0 ∧ (P.central x).valuation ≤ (B:ℤ)) :
    P.central 0 ≠ 0 := by
  have hinner :
      B+2*detBudget a hK cE tK ≤ max (B+2*detBudget a hK cE tK) 0 :=
    le_max_left _ _
  have houter :
      max (B+2*detBudget a hK cE tK) 0 ≤
        max (detBudget a hK cE tK) (max (B+2*detBudget a hK cE tK) 0) :=
    le_max_right _ _
  have hbig := (hinner.trans houter).trans_lt hM
  exact central_base_ne_zero P (by omega) hb hupper

end OriginalRCTerminalCertificate318
