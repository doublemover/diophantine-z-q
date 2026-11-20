module
public import OriginalRCTerminalCertificate318
import Lean.Elab.Tactic.Omega
public section

namespace OriginalRCTerminalBaseNumerator318
open OriginalRCTerminalAddress318 OriginalRCTerminalWindow318 OriginalRCTerminalCertificate318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem cast_reduction (M c : ℕ) (x : ℤ_[2]) :
    reduce M c (PadicInt.toZModPow M x) = PadicInt.toZModPow (M-c) x := by
  rw [reduce,ZMod.castHom_apply]
  exact PadicInt.cast_toZModPow (M-c) M (Nat.sub_le M c) x

/-- The literal old baseLift is pinned at precision M−c by the same
base numerator row and unit; one finite row does not give equality
of two integral lifts. The certificate is never replaced. -/
theorem baseLift_matches_candidate {b M c L : ℕ} (P : Certificate b M c L)
    (hc : c ≤ M) (U : ℤ_[2])
    (hU : (2 : Residue M)^c * testValue P.tests (constantDSlot L) 0 =
      testValue P.tests (constantFSlot L) 0 * PadicInt.toZModPow M U) :
    PadicInt.toZModPow (M-c) P.baseLift = PadicInt.toZModPow (M-c) U := by
  let δ := PadicInt.toZModPow M P.baseLift - PadicInt.toZModPow M U
  have hF : testValue P.tests (constantFSlot L) 0 * δ = 0 := by
    dsimp only [δ]
    rw [mul_sub,←P.baseRow,←hU,sub_self]
  have hA : (P.unit : Residue M) * ((2 : Residue M)^c * δ) = 0 := by
    rw [←mul_assoc,mul_comm (P.unit : Residue M) ((2 : Residue M)^c),←P.baseFactor]
    exact hF
  have hB : (2 : Residue M)^c * δ = 0 := by
    have hh := congrArg (fun x : Residue M => (↑(P.unit⁻¹) : Residue M) * x) hA
    simpa only [←mul_assoc,Units.inv_mul,one_mul,mul_zero] using hh
  have h := cancel_power hc δ hB
  dsimp only [δ] at h
  rw [map_sub,cast_reduction,cast_reduction] at h
  exact sub_eq_zero.mp h

/-- Candidate supplied by the genuine integral base numerator d₀(0)
and the genuine unit in F₀=2^c·unit. Only their residues are tested. -/
theorem baseLift_matches_true_normalized {b M c L : ℕ} (P : Certificate b M c L)
    (hc : c ≤ M) (D : ℤ_[2]) (u : ℤ_[2]ˣ)
    (hD : testValue P.tests (constantDSlot L) 0 = PadicInt.toZModPow M D)
    (hu : (P.unit : Residue M) = PadicInt.toZModPow M (u : ℤ_[2])) :
    PadicInt.toZModPow (M-c) P.baseLift =
      PadicInt.toZModPow (M-c) (((u⁻¹:ℤ_[2]ˣ):ℤ_[2]) * D) := by
  apply baseLift_matches_candidate P hc
  have hu' : PadicInt.toZModPow M (u : ℤ_[2]) *
      PadicInt.toZModPow M ((u⁻¹:ℤ_[2]ˣ):ℤ_[2]) = 1 := by
    rw [←map_mul,Units.mul_inv,map_one]
  rw [hD,P.baseFactor,hu,map_mul,mul_assoc,
    ←mul_assoc (PadicInt.toZModPow M (u:ℤ_[2])),hu',one_mul]

/-- Compare the same literal old certificate to a genuine base
candidate at its tested precision. The proof never identifies the
candidate with P.central 0 or overwrites P.baseLift. -/
theorem compare_normalized_candidate {b M c L : ℕ} (P : Certificate b M c L)
    (hM : 2*c ≤ M) (hb : (L+2)*(2^M-1) < b)
    (UZero : ℤ_[2]) (uZero : ℚ_[2])
    (hz : (UZero : ℚ_[2]) = (2 : ℚ_[2])^c * uZero)
    (hrow0 : (2 : Residue M)^c * testValue P.tests (constantDSlot L) 0 =
      testValue P.tests (constantFSlot L) 0 * PadicInt.toZModPow M UZero) :
    ∃ x : Fin b → ZMod 2, x ≠ 0 ∧
      (P.central x - uZero = 0 ∨
        ((M-2*c : ℕ) : ℤ) ≤ (P.central x - uZero).valuation) := by
  obtain ⟨x,hx,hm⟩ := exists_nonzero_matching_signRows b M (L+2) P.tests hb
  have hm' : ∀ i, testValue P.tests i x = testValue P.tests i 0 := hm
  obtain ⟨U, pos, uscale, hrow⟩ := P.otherLift x hx hm'
  let W : ScaledWindow M c L := {
    unit := P.unit
    fZero := testValue P.tests (constantFSlot L) 0
    fOther := testValue P.tests (constantFSlot L) x
    dZero := testValue P.tests (constantDSlot L) 0
    dOther := testValue P.tests (constantDSlot L) x
    uZero := PadicInt.toZModPow M UZero
    uOther := PadicInt.toZModPow M U
    negativeF := fun j => testValue P.tests (negativeSlot j) x
    positiveU := pos
    base_factor := P.baseFactor
    matching_f := hm' (constantFSlot L)
    matching_d := hm' (constantDSlot L)
    killed_tail := fun j => (hm' (negativeSlot j)).trans (P.baseNegative j)
    base_row := hrow0
    other_row := hrow }
  exact ⟨x,hx,central_value_double_loss hM W UZero U rfl rfl
    uZero (P.central x) hz uscale⟩

/-- It suffices to show that the SAME tested base numerator constant
would vanish. Even though the terminal certificate does not fix its
baseLift exactly from one finite row, the finite contradiction is exact. -/
theorem base_numerator_ne_zero {b M c L B : ℕ} (P : Certificate b M c L)
    (hM : B+2*c < M) (hb : (L+2)*(2^M-1) < b)
    (hupper : ∀ x, x ≠ 0 → P.central x ≠ 0 ∧ (P.central x).valuation ≤ (B:ℤ)) :
    testValue P.tests (constantDSlot L) 0 ≠ 0 := by
  intro hD
  have hrow : (2 : Residue M)^c * testValue P.tests (constantDSlot L) 0 =
      testValue P.tests (constantFSlot L) 0 * PadicInt.toZModPow M 0 := by
    simp only [hD,map_zero,mul_zero]
  obtain ⟨x,hx,hcmp⟩ := compare_normalized_candidate P (by omega : 2*c ≤ M)
    hb 0 0 (by simp only [PadicInt.coe_zero,mul_zero]) hrow
  rw [sub_zero] at hcmp
  have hu := hupper x hx
  rcases hcmp with hzero | hlower
  · exact hu.1 hzero
  · have hbits : B < M-2*c := by omega
    have hval := hu.2
    omega

end OriginalRCTerminalBaseNumerator318

#print axioms OriginalRCTerminalBaseNumerator318.baseLift_matches_true_normalized
#print axioms OriginalRCTerminalBaseNumerator318.base_numerator_ne_zero
