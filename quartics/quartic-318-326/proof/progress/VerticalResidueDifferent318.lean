module
public import DVRRamification318
public section
noncomputable section
namespace VerticalResidueDifferent318
open Module Algebra IsDiscreteValuationRing IsLocalRing LenstraVertical318

variable (A K B L:Type*) [CommRing A] [IsDomain A] [Field K]
    [CommRing B] [IsDomain B] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [Algebra A B] [Algebra B L] [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [CharZero K] [CharZero A] [CharZero B]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [IsTorsionFree A B]
    [IsFractionRing B L] [IsDiscreteValuationRing B]

/-- The vertical different bound from actual positive residue characteristic,
without supplying a nonunit certificate. -/
theorem vertical_bound (p d:ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    (hpd:p≤d) (hdegree:Module.finrank K L≤d) :
    differentExponent A B ≤
      2*(addVal B (p:B)).toNat*⌊Real.log (d:ℝ)/Real.log (p:ℝ)⌋₊ :=
  different_exponent_le_two_floor A K B L p d
    (DVRRamification318.residue_prime_not_unit B p) hpd hdegree

/-- The ramification product is computed from the actual uniformizer and
actual DVR valuations in the given field tower. -/
theorem ramification_value [IsDiscreteValuationRing A]
    (p:ℕ) [Fact p.Prime] (pi:A) (hpi:Irreducible pi) :
    (addVal B (p:B)).toNat=
      (addVal B (algebraMap A B pi)).toNat*(addVal A (p:A)).toNat := by
  have hf:Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hp0:(p:A)≠0 := by exact_mod_cast (Fact.out:p.Prime).ne_zero
  simpa only [map_natCast] using
    DVRRamification318.value_map_nat A B (algebraMap A B) hf pi hpi (p:A) hp0

/-- The source coefficient 2e e_p floor(log d/log p), with e and e_p the
actual uniformizer/p valuations. Neither a coefficient bound nor the
ramification multiplication identity is an input. -/
theorem ramified_vertical_bound [IsDiscreteValuationRing A]
    (p d:ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    (pi:A) (hpi:Irreducible pi) (hpd:p≤d) (hdegree:Module.finrank K L≤d) :
    differentExponent A B ≤
      2*(addVal B (algebraMap A B pi)).toNat*(addVal A (p:A)).toNat*
        ⌊Real.log (d:ℝ)/Real.log (p:ℝ)⌋₊ := by
  have h:=vertical_bound A K B L p d hpd hdegree
  rw [ramification_value A B p pi hpi] at h
  simpa only [mul_assoc] using h

end VerticalResidueDifferent318
