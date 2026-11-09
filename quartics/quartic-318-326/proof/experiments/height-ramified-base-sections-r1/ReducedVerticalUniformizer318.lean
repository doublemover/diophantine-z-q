module
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic
public section
noncomputable section
namespace ReducedVerticalUniformizer318
open IsLocalRing IsDiscreteValuationRing
set_option maxHeartbeats 400000
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

/-- A reduced special fiber rules out multiplicity greater than one in
an actual DVR. The chosen irreducible is only an intermediate DVR generator;
the conclusion identifies the original base parameter itself as a uniformizer. -/
theorem irreducible_of_reduced_quotient (x : B) (hx : x ≠ 0) (hxu : ¬IsUnit x)
    [IsReduced (B ⧸ Ideal.span ({x} : Set B))] : Irreducible x := by
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨n, u, hfactor⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hpi
  let q := Ideal.Quotient.mk (Ideal.span ({x} : Set B))
  have hxq : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  have hmul : q (u : B) * (q pi)^n = 0 := by
    rw [←map_pow, ←map_mul, ←hfactor]
    exact hxq
  have hpow : (q pi)^n = 0 := (Units.map q.toMonoidHom u).mul_right_eq_zero.mp hmul
  have hnil : IsNilpotent (q pi) := ⟨n, hpow⟩
  have hpimem : pi ∈ Ideal.span ({x} : Set B) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hnil.eq_zero
  have hmax : maximalIdeal B = Ideal.span ({x} : Set B) := by
    apply le_antisymm
    · rw [hpi.maximalIdeal_eq]
      apply Ideal.span_le.mpr
      intro y hy
      have hy' : y = pi := Set.mem_singleton_iff.mp hy
      simpa only [hy'] using hpimem
    · apply Ideal.span_le.mpr
      intro y hy
      have hy' : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact hxu
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal x hx hmax

/-- Exact reduced-fiber specialization for the original rational prime.
No restriction excluding the contact-collision primes 2,3,5,7 is present. -/
theorem prime_uniformizer (p : ℕ) (hp0 : (p : B) ≠ 0) (hpu : ¬IsUnit (p : B))
    [IsReduced (B ⧸ Ideal.span ({(p : B)} : Set B))] : Irreducible (p : B) :=
  irreducible_of_reduced_quotient (p : B) hp0 hpu

end ReducedVerticalUniformizer318
