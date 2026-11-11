module
public import PELMaximalQuotientProper318
public section
noncomputable section
namespace PELMaximalFiberCardinality318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalBranchLabels318 PELStabilizerLocusInvariant318 PELMaximalQuotientProper318
set_option maxHeartbeats 1600000

theorem labels_card : Nat.card Labels=16 := by
  norm_num [Labels,InertiaLabels318.V,Nat.card_eq_fintype_card,Fintype.card_pi]

theorem regular_stabilizer_card (p : UnlevelledBase) (hp : p∉nontrivialStabilizerLocus) :
    Nat.card (MulAction.stabilizer Labels p)=1 := by
  have hs : (MulAction.stabilizer Labels p : Set Labels)={1} := by
    ext g
    constructor
    · intro hg
      change g=1
      by_contra hne
      apply hp
      refine ⟨Multiplicative.toAdd g,?_,hg⟩
      intro hzero
      exact hne (congrArg Multiplicative.ofAdd hzero)
    · intro hg
      change g • p=p
      rw [Set.mem_singleton_iff.mp hg,one_smul]
  change Nat.card ↥(MulAction.stabilizer Labels p : Set Labels)=1
  rw [Nat.card_coe_set_eq,hs,Set.ncard_singleton]

theorem branch_stabilizer_card (i : Fin 5) (p : UnlevelledBase) (hp : p∈fixedLocus i) :
    Nat.card (MulAction.stabilizer Labels p)=2 := by
  let a : Labels := Multiplicative.ofAdd (InertiaLabels318.fiveLabels i)
  have ha : (1 : Labels)≠a := by
    intro h
    exact InertiaLabels318.five_labels_nonzero i (congrArg Multiplicative.toAdd h).symm
  have hs : (MulAction.stabilizer Labels p : Set Labels)={1,a} := by
    ext g
    have h := locus_stabilizer_iff i p hp (Multiplicative.toAdd g)
    change g • p=p ↔ g=1 ∨ g=a
    constructor
    · intro hg
      rcases h.mp hg with h0 | hi
      · exact Or.inl (congrArg Multiplicative.ofAdd h0)
      · exact Or.inr (congrArg Multiplicative.ofAdd hi)
    · rintro (rfl | rfl)
      · exact one_smul _ _
      · exact hp
  change Nat.card ↥(MulAction.stabilizer Labels p : Set Labels)=2
  rw [Nat.card_coe_set_eq,hs,Set.ncard_pair ha]

/-- Orbit-stabilizer is applied to the actual full original group and
its actual point stabilizer, not an independently chosen degree. -/
theorem fiber_times_stabilizer (p : UnlevelledBase) :
    Nat.card {x : UnlevelledBase // PELOriginalMaximalQuotient318.projection x=
      PELOriginalMaximalQuotient318.projection p} * Nat.card (MulAction.stabilizer Labels p)=16 := by
  have ho := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Labels p)
  have hf := Nat.card_congr (Equiv.setCongr (fiber_eq_orbit p))
  rw [Nat.card_prod] at ho
  rw [hf]
  exact ho.trans labels_card

/-- Every actual fiber has sixteen points off the branch image and
eight points on it. This does NOT count the number of branch fibers. -/
theorem original_fiber_card (q : MaximalBase) :
    Nat.card {x : UnlevelledBase // PELOriginalMaximalQuotient318.projection x=q}=
      if q∈branchImage then 8 else 16 := by
  classical
  obtain ⟨p,rfl⟩ := projection_surjective q
  have hm := fiber_times_stabilizer p
  by_cases hp : p∈nontrivialStabilizerLocus
  · obtain ⟨i,hi⟩ := (original_locus_union p).mp hp
    rw [branch_stabilizer_card i p hi] at hm
    rw [if_pos ((branch_image_iff p).mpr hp)]
    omega
  · rw [regular_stabilizer_card p hp,mul_one] at hm
    rw [if_neg (fun h => hp ((branch_image_iff p).mp h))]
    exact hm
end PELMaximalFiberCardinality318
