module
public import CTActualSelectedPadicValuation318
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.Valuation.Integral
public section
noncomputable section

namespace CTActualSelectedGlobalPrime318

open CTActualSelectedPadicLayer318 CTActualSelectedPadicValuation318
open IsLocalRing
open scoped NumberField

variable (p : ℕ) [Fact p.Prime] (M : GlobalLayer)
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (Pbar p) Γ) [(Padic.mulValuation (p := p)).HasExtension w]

/-- Images of the same global algebraic integers lie in the actual
selected valuation ring. No forward local integrality is used. -/
def integerEmbedding : 𝓞 M.toIntermediateField →+* selectedIntegers p M w :=
  ((layerEmbedding p M).toRingHom.comp
    (algebraMap (𝓞 M.toIntermediateField) M.toIntermediateField)).codRestrict
    (selectedIntegers p M w).toSubring fun x => by
      let v := selectedLayerValuation p M w
      let f := (layerEmbedding p M).toRingHom
      have h : IsIntegral ℤ (f (algebraMap (𝓞 M.toIntermediateField) M.toIntermediateField x)) :=
        map_isIntegral_int f x.isIntegral_coe
      exact (v.valuationSubring.integers.isIntegral_iff_v_le_one).1 h.tower_top

/-- The place determined by the literal closure embedding and its
valuation, rather than an arbitrarily chosen prime over p. -/
def selectedGlobalPrime : Ideal (𝓞 M.toIntermediateField) :=
  (maximalIdeal (selectedIntegers p M w)).comap (integerEmbedding p M w)

instance : (selectedGlobalPrime p M w).IsPrime :=
  Ideal.comap_isPrime _ _

theorem int_mem_selectedGlobalPrime (z : ℤ) :
    (z : 𝓞 M.toIntermediateField) ∈ selectedGlobalPrime p M w ↔ (p : ℤ) ∣ z := by
  change integerEmbedding p M w (z : 𝓞 M.toIntermediateField) ∈
    maximalIdeal (selectedIntegers p M w) ↔ _
  rw [map_intCast,Valuation.mem_maximalIdeal_iff]
  change w ((z : ℤ) : Pbar p) < 1 ↔ _
  rw [← map_intCast (algebraMap ℚ_[p] (Pbar p)),
    Valuation.HasExtension.val_map_lt_one_iff (Padic.mulValuation (p := p)) w]
  have hVal : ‖(z : ℚ_[p])‖ < 1 ↔ Padic.mulValuation (z : ℚ_[p]) < 1 := by
    simpa only [norm_one,map_one] using
      (Padic.norm_lt_norm_iff_mulValuation_lt (x := (z : ℚ_[p])) (y := (1 : ℚ_[p])))
  exact hVal.symm.trans (Padic.norm_intCast_lt_one_iff (p := p))

theorem selectedGlobalPrime_liesOver :
    (selectedGlobalPrime p M w).LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  constructor
  ext z
  rw [Ideal.mem_span_singleton]
  exact (int_mem_selectedGlobalPrime p M w z).symm

/-- Exact use of the old discriminant, at the place determined by the
retained closure embedding. This yields the characteristic-zero
localization which controls the new local finite image order. -/
theorem selectedGlobalPrime_unramified
    (hD : ¬ (p : ℤ) ∣ NumberField.discr M.toIntermediateField) :
    Algebra.IsUnramifiedAt ℤ (selectedGlobalPrime p M w) := by
  have hp : Prime (p : ℤ) := ((p : ℤ).prime_iff_natAbs_prime).2
    (by simpa using (Fact.out : p.Prime))
  exact ((NumberField.not_dvd_discr_iff_isUnramifiedIn M.toIntermediateField
    (𝓞 M.toIntermediateField) hp).1 hD) _
      inferInstance (selectedGlobalPrime_liesOver p M w)

end CTActualSelectedGlobalPrime318
