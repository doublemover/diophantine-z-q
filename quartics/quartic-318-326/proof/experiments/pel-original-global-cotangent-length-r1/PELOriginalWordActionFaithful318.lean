module
public import PELScalarCoarseKernel318
public section
noncomputable section
namespace PELOriginalWordActionFaithful318
open PELPositiveOrderNormalizer318 PELUnlevelledNormalizerAction318 PELUnlevelledComplexBase318
open PELScalarCoarseKernel318
set_option maxHeartbeats 1400000

/-- Equality of the actual automorphisms forces equality of original norm
parities, without any converse normalizer-kernel classification premise. -/
theorem parity_of_action_eq (g h : positiveNormalizer) (he : coarseAction g=coarseAction h) :
    PELPositiveOrderNormalizer318.parity g=PELPositiveOrderNormalizer318.parity h := by
  have hk : ∀ x,coarseAction (g⁻¹*h) x=x := by
    intro x
    rw [coarseAction_mul,←he,←coarseAction_mul,inv_mul_cancel,coarseAction_one]
  have hp := identity_has_trivial_parity (g⁻¹*h) hk
  rw [map_mul,map_inv,inv_mul_eq_one] at hp
  exact hp

/-- The16 ORIGINAL ordered prime words give16 DISTINCT holomorphic
coarse-base automorphisms. This is not inferred from16 abstract labels. -/
theorem original_word_action_injective :
    Function.Injective (fun v : InertiaLabels318.V => coarseAction (PELPositiveOrderNormalizer318.word v)) := by
  intro v w h
  have hp := parity_of_action_eq _ _ h
  rw [parity_word,parity_word] at hp
  exact congrArg Multiplicative.toAdd hp

theorem original_word_range_card :
    Nat.card (Set.range (fun v : InertiaLabels318.V => coarseAction (PELPositiveOrderNormalizer318.word v)))=16 := by
  rw [Nat.card_congr (Equiv.ofInjective _ original_word_action_injective).symm]
  rw [Nat.card_eq_fintype_card]
  norm_num [InertiaLabels318.V]
end PELOriginalWordActionFaithful318
