module
public import OriginalR47LiteralNodeCentre318
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public section
noncomputable section

namespace OriginalR47DyadicFixedReesCentre318

open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
open OriginalThickCentralReesChart318 (O I x y w)
universe u v
variable {D : Type u} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
variable {B : Type v} [CommRing B]
variable (q : D) (hq : Irreducible q) (d : ℕ)
variable (φ : O q d →+* B) (z : PrimeSpectrum B)

abbrev contracted : PrimeSpectrum (O q d) := PrimeSpectrum.comap φ z

/-- An actual normalized wild fixed-node map reads each of its two
oriented quotient axes as a unit times a positive power of the actual
cover axis. Do not use this equivalence to claim that any such map or
normalized whole R8 quotient has already been constructed. In the
application it is the genuine norm-axis map, with its fixed branch,
from the preceding dyadic normalization. -/
theorem retained_origin (a b X Y : B) (n r s : ℕ)
    (hr : r ≠ 0) (hs : s ≠ 0)
    (ha : a ∉ z.asIdeal) (hb : b ∉ z.asIdeal)
    (ax : φ (x q d) = a * X^r) (ay : φ (y q d) = b * Y^s)
    (hMark : Even n ↔ X ∈ z.asIdeal ∧ Y ∈ z.asIdeal) :
    Even n ↔ (contracted q d φ z).asIdeal = I q d := by
  let p := (contracted q d φ z).asIdeal
  letI : p.IsPrime := (contracted q d φ z).isPrime
  have hx : x q d ∈ p ↔ X ∈ z.asIdeal := by
    change φ (x q d) ∈ z.asIdeal ↔ X ∈ z.asIdeal
    rw [ax]
    constructor
    · intro h
      exact z.isPrime.mem_of_pow_mem r ((z.isPrime.mem_or_mem h).resolve_left ha)
    · intro h
      exact z.asIdeal.mul_mem_left _ (z.asIdeal.pow_mem_of_mem h r (Nat.pos_of_ne_zero hr))
  have hy : y q d ∈ p ↔ Y ∈ z.asIdeal := by
    change φ (y q d) ∈ z.asIdeal ↔ Y ∈ z.asIdeal
    rw [ay]
    constructor
    · intro h
      exact z.isPrime.mem_of_pow_mem s ((z.isPrime.mem_or_mem h).resolve_left hb)
    · intro h
      exact z.asIdeal.mul_mem_left _ (z.asIdeal.pow_mem_of_mem h s (Nat.pos_of_ne_zero hs))
  constructor
  · intro h
    obtain ⟨hX,hY⟩ := hMark.mp h
    have hₓ := hx.mpr hX
    have hᵧ := hy.mpr hY
    have hpw : w q d ∈ p := by
      apply (inferInstance : p.IsPrime).mem_of_pow_mem (d+2)
      change (algebraMap D (O q d) q) ^ (d+2) ∈ p
      rw [← map_pow,← node_relation]
      exact p.mul_mem_left _ hₓ
    apply ((OriginalR47LiteralNodeCentre318.maximal_of_dvr q d hq).eq_of_le
      (inferInstance : p.IsPrime).ne_top ?_).symm
    apply Ideal.span_le.mpr
    intro v hv
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact hₓ
    · exact hᵧ
    · exact hpw
  · intro h
    have hₓ : x q d ∈ p := h.symm ▸ Ideal.subset_span (by simp [I])
    have hᵧ : y q d ∈ p := h.symm ▸ Ideal.subset_span (by simp [I])
    exact hMark.mpr ⟨hx.mp hₓ,hy.mp hᵧ⟩

end OriginalR47DyadicFixedReesCentre318

#print axioms OriginalR47DyadicFixedReesCentre318.retained_origin
