module
public import PELOriginalStabilizerUniqueness318
public import PELPositiveNormalizerNormalForm318
public section
noncomputable section
namespace PELFullNormalizerAction318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELPositiveOrderNormalizer318 PELUnlevelledNormalizerAction318 PELUnlevelledComplexBase318
open PELNormOneBaseAction318 PELJointNormOneAction318 PELOriginalPrimeBaseInvolutions318
open PELOriginalElementaryAction318 PELPositiveNormalizerNormalForm318
open PELOriginalStabilizerUniqueness318 PELOriginalLabeledFixedOrbits318
set_option maxHeartbeats 1800000

/-- The FULL original positive normalizer action factors through its
actual original parity, with no support or normal-form hypothesis. -/
theorem actual_action_factorization (g : positiveNormalizer) (x : UnlevelledBase) :
    coarseAction g x=PELPositiveOrderNormalizer318.parity g • x := by
  obtain ⟨q,v,label,hv,hg⟩ := normal_form g
  have hp := normal_form_parity g q v label hv hg
  let u : normOneUnits := ⟨v,(mem_normOneUnits v).mpr hv⟩
  have hs : (g.val:B)=(q:ℚ) • (((originalNormalizer u)*word label).val:B) := by
    have he := congrArg (fun z : Bˣ => (z:B)) hg
    change (g.val:B)=algebraMap ℚ B (q:ℚ)*((v:order):B)*
      (PELInertiaPrimeWord318.word label:B) at he
    change (g.val:B)=(q:ℚ) • (((v:order):B)*(PELInertiaPrimeWord318.word label:B))
    simpa only [Algebra.smul_def,mul_assoc] using he
  rw [scalar_related_action g (originalNormalizer u*word label) (q:ℚ) q.ne_zero hs,
    coarseAction_mul,norm_one_trivial,hp] <;> rfl

/-- Equality of any two actual normalizer automorphisms is exactly
original parity equality, not merely equality within the displayed16 words. -/
theorem actual_action_eq_iff (g h : positiveNormalizer) :
    (∀ x,coarseAction g x=coarseAction h x) ↔
      PELPositiveOrderNormalizer318.parity g=PELPositiveOrderNormalizer318.parity h := by
  constructor
  · intro he
    apply action_faithful
    intro x
    simpa only [←actual_action_factorization] using he x
  · intro hp x
    rw [actual_action_factorization,actual_action_factorization,hp]

theorem actual_kernel_iff (g : positiveNormalizer) :
    (∀ x,coarseAction g x=x) ↔ PELPositiveOrderNormalizer318.parity g=1 := by
  have h := actual_action_eq_iff g 1
  simpa only [coarseAction_one,map_one] using h

/-- The original16 words exhaust the FULL normalizer action on this same
analytic curve, retaining the exact parity label of every normalizer. -/
theorem original_words_exhaust (g : positiveNormalizer) :
    coarseAction g=coarseAction (word (Multiplicative.toAdd (PELPositiveOrderNormalizer318.parity g))) := by
  funext x
  rw [actual_action_factorization,actual_action_factorization,parity_word]

theorem actual_action_range :
    Set.range (fun g : positiveNormalizer => coarseAction g)=
      Set.range (fun v : InertiaLabels318.V => coarseAction (word v)) := by
  ext f
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨Multiplicative.toAdd (PELPositiveOrderNormalizer318.parity g),(original_words_exhaust g).symm⟩
  · rintro ⟨v,rfl⟩
    exact ⟨word v,rfl⟩

theorem actual_action_card : Nat.card (Set.range (fun g : positiveNormalizer => coarseAction g))=16 := by
  rw [actual_action_range]
  exact PELOriginalWordActionFaithful318.original_word_range_card

/-- Full positive-normalizer stabilizers at the five ORIGINAL points are
exactly the two original parity classes. This does not exhaust branch orbits. -/
theorem original_point_full_stabilizer (i : Fin 5) (g : positiveNormalizer) :
    coarseAction g (originalPoint i)=originalPoint i ↔
      PELPositiveOrderNormalizer318.parity g=1 ∨
      PELPositiveOrderNormalizer318.parity g=Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) := by
  rw [actual_action_factorization]
  have h := original_point_stabilizer_iff i (Multiplicative.toAdd (PELPositiveOrderNormalizer318.parity g))
  constructor
  · intro hf
    rcases h.mp hf with he | he
    · exact Or.inl (congrArg Multiplicative.ofAdd he)
    · exact Or.inr (congrArg Multiplicative.ofAdd he)
  · rintro (he | he)
    · apply h.mpr
      exact Or.inl (congrArg Multiplicative.toAdd he)
    · apply h.mpr
      exact Or.inr (congrArg Multiplicative.toAdd he)
end PELFullNormalizerAction318
