module
public import OriginalPrimeThreeNormalizedLocalIdentification318
public import PrimeThreeLocalizationQuotient318
public section
noncomputable section
namespace OriginalPrimeThreeNormalizedSpecialFiber318
open OriginalPrimeThreeLocalOrderQuotient318
open OriginalPrimeThreeNormalizedLocalIdentification318
open PrimeThreeLocalizationQuotient318

attribute [local instance] OriginalIntegerNormalizationMap318.closureAlgebra
attribute [local instance] OriginalPrimeThreeNormalizedLocalIdentification318.closureLocalAlgebra

/-- The normalization's denominators are exactly the integer coefficients
prime to three, with the same inclusion into the actual local order. -/
local instance normalizedCoefficientLocalization :
    IsLocalization (PrimeThreeLocalizationQuotient318.denominators Closure) LocalOrder := by
  change IsLocalization (Algebra.algebraMapSubmonoid Closure
    PrimeThreeCoefficientLocalization318.primeIdeal.primeCompl) LocalOrder
  rw [← closureDenominators_eq_integer]
  exact actual_normalized_localization

@[expose] def originalToLocalFiber : Fiber Order ≃+* Fiber LocalOrder :=
  quotientEquiv Order LocalOrder

@[expose] def normalizedToLocalFiber : Fiber Closure ≃+* Fiber LocalOrder :=
  quotientEquiv Closure LocalOrder

/-- The ACTUAL untwisted normalized finite chart has the same entire
mod-three fiber as the original integral order. This does not assert
regularity, smoothness, or a result for a different twist or infinity chart. -/
@[expose] def normalizedFiberEquiv : Fiber Order ≃+* Fiber Closure :=
  originalToLocalFiber.trans normalizedToLocalFiber.symm

/-- The special-fiber identification is induced by the exact original
order-to-normalization inclusion. It fixes every coefficient and root. -/
@[simp] theorem normalizedFiberEquiv_on_order (a : Order) :
    normalizedFiberEquiv (Ideal.Quotient.mk (threeIdeal Order) a) =
      Ideal.Quotient.mk (threeIdeal Closure) (algebraMap Order Closure a) := by
  apply normalizedToLocalFiber.injective
  change normalizedToLocalFiber (normalizedToLocalFiber.symm
    (originalToLocalFiber (Ideal.Quotient.mk (threeIdeal Order) a))) = _
  rw [RingEquiv.apply_symm_apply]
  change quotientEquiv Order LocalOrder (Ideal.Quotient.mk (threeIdeal Order) a) =
    quotientEquiv Closure LocalOrder
      (Ideal.Quotient.mk (threeIdeal Closure) (algebraMap Order Closure a))
  rw [quotientEquiv_mk, quotientEquiv_mk]
  change Ideal.Quotient.mk (threeIdeal LocalOrder) (algebraMap Order LocalOrder a) =
    Ideal.Quotient.mk (threeIdeal LocalOrder) (closureToLocal (algebraMap Order Closure a))
  rw [closureToLocal_on_order]

/-- The literal quotient map induced by the normalization inclusion. -/
@[expose] def normalizationFiberMap : Fiber Order →+* Fiber Closure :=
  Ideal.quotientMap (threeIdeal Closure) (algebraMap Order Closure)
    (Ideal.map_le_iff_le_comap.mp (le_of_eq (threeIdeal_map Order Closure)))

theorem normalizedFiberEquiv_eq_canonical :
    normalizedFiberEquiv.toRingHom = normalizationFiberMap := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact normalizedFiberEquiv_on_order a

theorem normalizationFiberMap_bijective : Function.Bijective normalizationFiberMap := by
  rw [← normalizedFiberEquiv_eq_canonical]
  exact normalizedFiberEquiv.bijective

/-- The coefficient model is now identified with the ACTUAL normalized
special fiber, through the original order and the canonical quotient map. -/
@[expose] def normalizedFiberPresentation : Fiber Closure ≃+*
    FourRootOrder318.Order OriginalPrimeThreeActualQuotient318.coefficient :=
  normalizedFiberEquiv.symm.trans
    ((Ideal.quotEquivOfEq
      OriginalPrimeThreeActualQuotient318.extendedIdeal_eq_three.symm).trans
        OriginalPrimeThreeActualQuotient318.quotientEquiv)

/-- Reducedness belongs to the literal normalized chart modulo three,
not only to a generic four-root model or an already-localized quotient. -/
theorem actual_normalized_quotient_reduced : IsReduced (Fiber Closure) := by
  letI : IsReduced (Fiber Order) :=
    OriginalPrimeThreeActualQuotient318.actual_quotient_reduced
  exact isReduced_of_injective normalizedFiberEquiv.symm.toRingHom
    normalizedFiberEquiv.symm.injective

end OriginalPrimeThreeNormalizedSpecialFiber318
