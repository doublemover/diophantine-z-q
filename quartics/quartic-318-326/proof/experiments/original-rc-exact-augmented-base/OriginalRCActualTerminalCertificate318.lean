module
public import OriginalRCLiteralTerminalRows318
import Lean.Elab.Tactic.Omega

open scoped BigOperators

public section

noncomputable section

namespace OriginalRCActualTerminalCertificate318
open OriginalRCTerminalCertificate318 OriginalRCTerminalWindow318 OriginalRCLiteralTerminalRows318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {R G : Type*} [CommRing R] [Group G]
variable {b M L c : ℕ}

abbrev Address (b : ℕ) := Fin b → ZMod 2

theorem normal_constant_map (U : PowerSeries ℤ_[2]) :
    PowerSeries.constantCoeff (PowerSeries.map (PadicInt.toZModPow M) U) =
      PadicInt.toZModPow M (PowerSeries.constantCoeff U) := by
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]

/-- The already chosen scaled *regular* series is an actual integral
lift. This is a finite ring image, not t=0 on the Laurent ring. -/
def finiteRegular (M : ℕ) (U : PowerSeries ℤ_[2]) : Series M :=
  HahnSeries.ofPowerSeries ℤ (Residue M) (PowerSeries.map (PadicInt.toZModPow M) U)

theorem finiteRegular_eq (p : ℕ) (U : PowerSeries ℤ_[2]) :
    finiteRegular p U = HahnSeries.ofPowerSeries ℤ (Residue p)
      (PowerSeries.map (PadicInt.toZModPow p) U) := rfl

section

variable (label : Finset (Fin b) ≃ G) (rho : R →+* Series M)
  (chi : Address b → G →* Series M) (f d : MonoidAlgebra R G)

abbrev originalRows : Tests b M L := literalTests label rho f d

/-- Old scaled row obtained from the exact same finite original product. -/
theorem normalized_row
    (x : Address b) (U : PowerSeries ℤ_[2])
    (hchi : ∀ S : Finset (Fin b), chi x (label S) =
      ∏ j ∈ S, (if x j = 0 then (1 : Series M) else -1))
    (hcut : ∀ n : ℤ, n < -(L : ℤ) → (evaluate rho (chi x) f).coeff n = 0)
    (hprod : HahnSeries.C ((2 : Residue M)^c) * evaluate rho (chi x) d =
      evaluate rho (chi x) f * finiteRegular M U) :
    (2 : Residue M)^c * testValue (originalRows label rho f d) (constantDSlot L) x =
      testValue (originalRows label rho f d) (constantFSlot L) x *
          PadicInt.toZModPow M (PowerSeries.constantCoeff U) +
        ∑ j : Fin L, testValue (originalRows label rho f d) (negativeSlot j) x *
          PadicInt.toZModPow M (PowerSeries.coeff (j.val+1) U) := by
  simpa only [normal_constant_map, PowerSeries.coeff_map, originalRows] using
    scaled_test_row label rho (chi x) f d x hchi
      (PowerSeries.map (PadicInt.toZModPow M) U) c hcut hprod

/-- Populate the existing Certificate interface from the literal old
f,d rows. The base lift is the supplied, already designated integral
lift, fixed by its exact regular-series constant; it is never reselected
by a finite residue. Other analytic lifts are requested only after all
L+2 computed tests match. -/
def from_original
    (central : Address b → ℚ_[2]) (unit : ℤ_[2]ˣ)
    (baseLift : ℤ_[2]) (U0 : PowerSeries ℤ_[2])
    (hchi : ∀ (x : Address b) (S : Finset (Fin b)), chi x (label S) =
      ∏ j ∈ S, (if x j = 0 then (1 : Series M) else -1))
    (hbase : PowerSeries.constantCoeff U0 = baseLift)
    (hcenter : (baseLift : ℚ_[2]) = (2 : ℚ_[2])^c * central 0)
    (hF0 : (evaluate rho (chi 0) f).coeff 0 =
      (2 : Residue M)^c * PadicInt.toZModPow M (unit : ℤ_[2]))
    (hnegative : ∀ n : ℤ, n < 0 → (evaluate rho (chi 0) f).coeff n = 0)
    (hprod0 : HahnSeries.C ((2 : Residue M)^c) * evaluate rho (chi 0) d =
      evaluate rho (chi 0) f * finiteRegular M U0)
    (other : ∀ (x : Address b), x ≠ 0 →
      (∀ i : Fin (L+2), testValue (originalRows label rho f d) i x =
        testValue (originalRows label rho f d) i 0) →
      ∃ U : PowerSeries ℤ_[2],
        ((PowerSeries.constantCoeff U : ℤ_[2]) : ℚ_[2]) = (2 : ℚ_[2])^c * central x ∧
        (∀ n : ℤ, n < -(L : ℤ) → (evaluate rho (chi x) f).coeff n = 0) ∧
        HahnSeries.C ((2 : Residue M)^c) * evaluate rho (chi x) d =
          evaluate rho (chi x) f * finiteRegular M U) :
    Certificate b M c L where
  tests := originalRows label rho f d
  central := central
  unit := Units.map (PadicInt.toZModPow M).toMonoidHom unit
  baseLift := baseLift
  baseScaled := hcenter
  baseFactor := by
    rw [originalRows, literal_F_test label rho (chi 0) f d 0 (hchi 0)]
    exact hF0
  baseNegative j := by
    rw [originalRows, literal_negative_test label rho (chi 0) f d 0 (hchi 0)]
    exact hnegative _ (by omega)
  baseRow := by
    have hcut : ∀ n : ℤ, n < -(L : ℤ) → (evaluate rho (chi 0) f).coeff n = 0 :=
      fun n hn => hnegative n (by omega)
    have hneg (j : Fin L) :
        testValue (originalRows label rho f d) (negativeSlot j) 0 = 0 := by
      rw [originalRows, literal_negative_test label rho (chi 0) f d 0 (hchi 0)]
      exact hnegative _ (by omega)
    simpa only [hbase, hneg, zero_mul, Finset.sum_const_zero, add_zero] using
      normalized_row label rho chi f d 0 U0 (hchi 0) hcut hprod0
  otherLift x hx hmatch := by
    obtain ⟨U, hU, hcut, hprod⟩ := other x hx hmatch
    exact ⟨PowerSeries.constantCoeff U,
      fun j => PadicInt.toZModPow M (PowerSeries.coeff (j.val+1) U),
      hU, normalized_row label rho chi f d x U (hchi x) hcut hprod⟩

end

end OriginalRCActualTerminalCertificate318

#print axioms OriginalRCActualTerminalCertificate318.from_original
