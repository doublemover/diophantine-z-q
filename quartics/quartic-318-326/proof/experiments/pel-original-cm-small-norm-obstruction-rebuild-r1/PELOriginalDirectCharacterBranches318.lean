module
public import PELOriginalDirectBranchEnumeration318
public import PELOriginalCharacterBranches318
public section
noncomputable section
namespace PELOriginalDirectCharacterBranches318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalBranchLabels318 PELOriginalLabeledFixedOrbits318
open PELOriginalFiniteRamification318 PELOriginalCharacterQuotient318
open PELOriginalCharacterBranches318 (CharacterBranchValues visible_labels_card)

/-- Complete branch values of the SAME four complex character quotient
maps, now from exhaustive original normalizer classification rather than
an unproduced genus/RH input. The quotient carriers and maps are unchanged. -/
theorem branch_values_iff (i : Fin 4) (q : MaximalBase) :
    q ∈ CharacterBranchValues i ↔ ∃ j : Fin 5,
      InertiaLabels318.fiveLabels j i ≠ 0 ∧
        q = PELOriginalMaximalQuotient318.projection (originalPoint j) := by
  obtain ⟨x, rfl⟩ := PELOriginalMaximalQuotient318.projection_surjective q
  constructor
  · intro hc
    change Nat.card {y : CharacterBase i // toMaximal i y =
      PELOriginalMaximalQuotient318.projection x} = 1 at hc
    by_cases hx : x ∈ nontrivialStabilizerLocus
    · obtain ⟨j, hj⟩ := (original_locus_union x).mp hx
      refine ⟨j, ?_, (PELOriginalDirectBranchEnumeration318.original_fixed_locus_one_orbit
        j x).mp hj⟩
      intro hz
      have hh := branch_fiber_card i j x hj
      rw [if_pos hz] at hh
      omega
    · have hh := regular_fiber_card i x hx
      omega
  · rintro ⟨j, hj, he⟩
    change Nat.card {y : CharacterBase i // toMaximal i y =
      PELOriginalMaximalQuotient318.projection x} = 1
    rw [he]
    exact (branch_fiber_card i j (originalPoint j) (original_label_fixes j)).trans
      (if_neg hj)

/-- The complete actual branch-value subtype is explicitly enumerated by
exactly the four visible OLD labels. -/
@[expose] def branchEnumeration (i : Fin 4) :
    {j : Fin 5 // InertiaLabels318.fiveLabels j i ≠ 0} ≃ CharacterBranchValues i :=
  Equiv.ofBijective
    (fun j => ⟨PELOriginalMaximalQuotient318.projection (originalPoint j.val),
      (branch_values_iff i _).mpr
        ⟨j.val,j.property,rfl⟩⟩)
    ⟨by
      intro j k he
      apply Subtype.ext
      apply displayed_injective
      apply Subtype.ext
      exact congrArg Subtype.val he,
    by
      intro q
      obtain ⟨j,hj,he⟩ := (branch_values_iff i q.val).mp q.property
      refine ⟨⟨j,hj⟩,?_⟩
      apply Subtype.ext
      exact he.symm⟩

theorem exactly_four_actual_branch_values (i : Fin 4) :
    Nat.card (CharacterBranchValues i) = 4 := by
  rw [← Nat.card_congr (branchEnumeration i),
    Nat.card_eq_fintype_card]
  exact visible_labels_card i

end PELOriginalDirectCharacterBranches318
