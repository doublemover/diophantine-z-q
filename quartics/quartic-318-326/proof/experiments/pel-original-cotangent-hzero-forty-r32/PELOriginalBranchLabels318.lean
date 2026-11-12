module
public import PELOriginalFixedTangent318
public import PELPositiveEllipticLabels318
public section
noncomputable section
namespace PELOriginalBranchLabels318
open QuaternionicJointPeriodTopology318 PELPositiveOrderNormalizer318
open PELUnlevelledComplexBase318 PELUnlevelledNormalizerAction318 PELOriginalElementaryAction318
open PELOriginalLabeledFixedOrbits318 PELOriginalStabilizerUniqueness318
set_option maxHeartbeats 1800000

/-- Every nontrivial full-normalizer stabilizer at EVERY actual coarse
point has one of the five original labels. The upstairs representative and
strict trace bound are constructed from this very fixed point. -/
theorem full_fixed_parity (g : positiveNormalizer) (x : UnlevelledBase)
    (hp : PELPositiveOrderNormalizer318.parity g≠1) (hf : coarseAction g x=x) :
    ∃ i : Fin 5,PELPositiveOrderNormalizer318.parity g=
      Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) := by
  obtain ⟨τ,rfl⟩ := projection_surjective x
  obtain ⟨n,hn,hna,hnp⟩ := PELFixedNormalizerLift318.original_fixed_lift g τ hf
  have hnp0 : PELPositiveOrderNormalizer318.parity n≠1 := by rwa [hnp]
  have hb := PELFixedNormalizerStrictTrace318.fixed_nontrivial_parity n τ hn hnp0
  obtain ⟨i,hi⟩ := PELPositiveEllipticLabels318.original_five_labels n hb
  exact ⟨i,hnp.symm.trans hi⟩

theorem original_fixed_label (v : InertiaLabels318.V) (x : UnlevelledBase)
    (hv : v≠0) (hf : Multiplicative.ofAdd v • x=x) :
    ∃ i : Fin 5,v=InertiaLabels318.fiveLabels i := by
  have hp : PELPositiveOrderNormalizer318.parity (word v)≠1 := by
    rw [parity_word]
    intro he
    exact hv (congrArg Multiplicative.toAdd he)
  obtain ⟨i,hi⟩ := full_fixed_parity (word v) x hp hf
  rw [parity_word] at hi
  exact ⟨i,congrArg Multiplicative.toAdd hi⟩

theorem no_other_fixed_labels (v : InertiaLabels318.V) (hv : v≠0)
    (hlabels : ∀ i : Fin 5,v≠InertiaLabels318.fiveLabels i) :
    ∀ x : UnlevelledBase,Multiplicative.ofAdd v • x≠x := by
  intro x hf
  obtain ⟨i,hi⟩ := original_fixed_label v x hv hf
  exact hlabels i hi

@[expose] def fixedLocus (i : Fin 5) : Set UnlevelledBase :=
  {x | Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) • x=x}
@[expose] def nontrivialStabilizerLocus : Set UnlevelledBase :=
  {x | ∃ v : InertiaLabels318.V,v≠0 ∧ Multiplicative.ofAdd v • x=x}

/-- Exact union of the FIVE labeled fixed loci, not a claim that each
locus is one orbit or that the geometric quotient has five branch points. -/
theorem original_locus_union (x : UnlevelledBase) :
    x∈nontrivialStabilizerLocus ↔ ∃ i : Fin 5,x∈fixedLocus i := by
  constructor
  · rintro ⟨v,hv,hf⟩
    obtain ⟨i,rfl⟩ := original_fixed_label v x hv hf
    exact ⟨i,hf⟩
  · rintro ⟨i,hf⟩
    exact ⟨InertiaLabels318.fiveLabels i,InertiaLabels318.five_labels_nonzero i,hf⟩

theorem fixed_locus_index_unique (i j : Fin 5) (x : UnlevelledBase)
    (hi : x∈fixedLocus i) (hj : x∈fixedLocus j) : i=j := by
  apply InertiaLabels318.five_labels_injective
  exact unique_nonzero_stabilizer x _ _ (InertiaLabels318.five_labels_nonzero i)
    (InertiaLabels318.five_labels_nonzero j) hi hj

theorem original_locus_nonempty (i : Fin 5) : (fixedLocus i).Nonempty :=
  ⟨originalPoint i,original_label_fixes i⟩

/-- Full stabilizer law at ANY point in a labeled fixed locus. -/
theorem locus_stabilizer_iff (i : Fin 5) (x : UnlevelledBase) (hx : x∈fixedLocus i)
    (v : InertiaLabels318.V) : Multiplicative.ofAdd v • x=x ↔
      v=0 ∨ v=InertiaLabels318.fiveLabels i := by
  constructor
  · intro hf
    by_cases hv : v=0
    · exact Or.inl hv
    · exact Or.inr (unique_nonzero_stabilizer x v _ hv
        (InertiaLabels318.five_labels_nonzero i) hf hx)
  · rintro (rfl | rfl)
    · exact one_smul _ _
    · exact hx
end PELOriginalBranchLabels318
