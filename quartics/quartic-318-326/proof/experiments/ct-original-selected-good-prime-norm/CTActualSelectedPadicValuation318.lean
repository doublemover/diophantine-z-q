module
public import CTActualSelectedPadicLayer318
public import CTPadicSelectedValuationRing318
public section
noncomputable section

namespace CTActualSelectedPadicValuation318

open CTActualSelectedPadicLayer318
open scoped CTPadicSelectedValuationRing318 BigOperators

variable (p : ℕ) [Fact p.Prime] (M : GlobalLayer)
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- The valuation on the retained finite layer is the restriction of
the chosen valuation on the same literal algebraic closure. -/
abbrev selectedLayerValuation (w : Valuation (Pbar p) Γ) :
    Valuation (localField p M) Γ :=
  w.comap ((localField p M).val.toRingHom)

instance (w : Valuation (Pbar p) Γ) [(Padic.mulValuation (p := p)).HasExtension w] :
    (Padic.mulValuation (p := p)).HasExtension (selectedLayerValuation p M w) where
  val_isEquiv_comap := by
    intro x y
    change Padic.mulValuation x ≤ Padic.mulValuation y ↔
      w ((localField p M).val (algebraMap ℚ_[p] (localField p M) x)) ≤
        w ((localField p M).val (algebraMap ℚ_[p] (localField p M) y))
    rw [(localField p M).val.commutes x,(localField p M).val.commutes y]
    exact (Valuation.HasExtension.val_map_le_iff (Padic.mulValuation (p := p)) w x y).symm

variable (w : Valuation (Pbar p) Γ) [(Padic.mulValuation (p := p)).HasExtension w]

abbrev selectedIntegers := (selectedLayerValuation p M w).valuationSubring

/-- Local norm comparison on the SAME finite layer and closure valuation.
Only the two stated arithmetic consequences of the place comparison
are still premises; the p-adic integral basis/valuation-one scalar
compatibility is produced internally. -/
theorem selected_actual_unit_norm
    (hInt : ∀ x : localField p M, w (x : Pbar p) ≤ 1 → IsIntegral ℤ_[p] x)
    (hI : (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (selectedIntegers p M w)) =
      IsLocalRing.maximalIdeal (selectedIntegers p M w))
    (u : (selectedIntegers p M w)ˣ)
    (hu : ∀ σ : localField p M ≃ₐ[ℚ_[p]] localField p M,
      σ (u : selectedIntegers p M w) = (u : selectedIntegers p M w)) :
    ∃ z : (selectedIntegers p M w)ˣ,
       (∏ σ : localField p M ≃ₐ[ℚ_[p]] localField p M, σ (z : selectedIntegers p M w)) =
          (u : selectedIntegers p M w) :=
  CTPadicSelectedValuationRing318.actual_norm_onto_fixed_units
    (selectedLayerValuation p M w) hInt hI u hu

end CTActualSelectedPadicValuation318
