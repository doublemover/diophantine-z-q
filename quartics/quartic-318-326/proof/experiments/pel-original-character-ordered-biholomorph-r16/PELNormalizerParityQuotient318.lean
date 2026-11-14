module
public import PELPositiveOrderNormalizer318
public import Mathlib.GroupTheory.QuotientGroup.Basic
public section
noncomputable section
namespace PELNormalizerParityQuotient318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELPositiveOrderNormalizer318
set_option maxHeartbeats 1000000

/-- This quotient is by the KERNEL OF THE ACTUAL NORM-PARITY MAP. Identifying
that kernel with rational scalars times integral units remains separate. -/
abbrev QuotientNormalizer := positiveNormalizer ⧸ parity.ker

@[expose] def quotientEquiv : QuotientNormalizer ≃* Multiplicative InertiaLabels318.V :=
  QuotientGroup.quotientKerEquivOfRightInverse parity
    (fun v => word (Multiplicative.toAdd v)) (fun v => parity_word _)

theorem quotientEquiv_mk (u : positiveNormalizer) :
    quotientEquiv (QuotientGroup.mk u)=parity u := rfl

noncomputable instance quotientFintype : Fintype QuotientNormalizer :=
  Fintype.ofEquiv (Multiplicative InertiaLabels318.V) quotientEquiv.symm.toEquiv

theorem quotient_card : Fintype.card QuotientNormalizer=16 := by
  rw [Fintype.card_congr quotientEquiv.toEquiv]
  change Fintype.card (Fin 4 → ZMod 2)=16
  norm_num

/-- The actual normalizer words give16 DISTINCT quotient elements. -/
theorem word_class_injective : Function.Injective
    (fun v : InertiaLabels318.V => (QuotientGroup.mk (word v):QuotientNormalizer)) := by
  intro v w h
  have hh := congrArg (fun q:QuotientNormalizer => Multiplicative.toAdd (quotientEquiv q)) h
  simpa only [quotientEquiv_mk,parity_word,toAdd_ofAdd] using hh

/-- Same scalar/normalizer arithmetic, with no geometric deck-action claim. -/
theorem every_class (q : QuotientNormalizer) :
    ∃ v : InertiaLabels318.V,QuotientGroup.mk (word v)=q := by
  refine ⟨Multiplicative.toAdd (quotientEquiv q),?_⟩
  apply quotientEquiv.injective
  rw [quotientEquiv_mk,parity_word,ofAdd_toAdd]

/-- No two different original labels become identified in this actual
normalizer parity quotient. -/
theorem original_five_classes_injective : Function.Injective
    (fun i : Fin 5 => (QuotientGroup.mk (word (InertiaLabels318.fiveLabels i)):
      QuotientNormalizer)) :=
  word_class_injective.comp InertiaLabels318.five_labels_injective
/-- Actual fixed-point inertia representatives have the original five
labels in this quotient, via the constructed original integral units. -/
theorem inertia_class (i : Fin 5) :
    (QuotientGroup.mk (inertiaElement i):QuotientNormalizer)=
      QuotientGroup.mk (word (InertiaLabels318.fiveLabels i)) := by
  apply quotientEquiv.injective
  rw [quotientEquiv_mk,quotientEquiv_mk,parity_inertia,parity_word]

theorem inertia_classes_injective : Function.Injective
    (fun i : Fin 5 => (QuotientGroup.mk (inertiaElement i):QuotientNormalizer)) := by
  intro i j h
  change (QuotientGroup.mk (inertiaElement i):QuotientNormalizer)=
    QuotientGroup.mk (inertiaElement j) at h
  rw [inertia_class,inertia_class] at h
  exact original_five_classes_injective h

end PELNormalizerParityQuotient318
