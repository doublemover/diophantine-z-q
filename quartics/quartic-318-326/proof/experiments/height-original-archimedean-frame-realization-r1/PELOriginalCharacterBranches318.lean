module
public import PELOriginalCharacterQuotient318
public section
noncomputable section
namespace PELOriginalCharacterBranches318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalBranchLabels318 PELOriginalLabeledFixedOrbits318
open PELOriginalFiniteRamification318 PELOriginalGenusBranchSqueeze318
open PELOriginalCharacterQuotient318

/-- The excluded contact coordinates are105,70,42,30, in their original order. -/
@[expose] def omitted (i : Fin 4) : Fin 5 := ![3,2,1,0] i
lemma omitted_label : ∀ (i : Fin 4) (j : Fin 5),
    InertiaLabels318.fiveLabels j i = 0 ↔ j = omitted i := by decide
lemma omitted_divisor : ∀ i : Fin 4,
    InertiaLabels318.divisor (InertiaLabels318.fiveLabels (omitted i)) =
      (![105,70,42,30] : Fin 4 → ℕ) i := by decide
lemma visible_labels_card : ∀ i : Fin 4,
    Fintype.card {j : Fin 5 // InertiaLabels318.fiveLabels j i ≠ 0} = 4 := by decide

/-- Branch VALUES of this actual intermediate map, defined by its actual
full fiber cardinality, not by declaring the desired four-point list. -/
@[expose] def CharacterBranchValues (i : Fin 4) : Set MaximalBase :=
  {q | Nat.card {y : CharacterBase i // toMaximal i y = q} = 1}

variable (sourceGenus quotientGenus : ℕ) (hupper : sourceGenus ≤ 5)
    (hRH : 2 * (sourceGenus : ℤ) - 2 =
      16 * (2 * (quotientGenus : ℤ) - 2) + (Fintype.card Ramification : ℤ))

include hupper hRH in
/-- Completeness comes from the SAME original full-curve RH/genus squeeze.
The intermediate covers inherit their four branches; no published elliptic
model, genus-one assumption, or replacement action is used. -/
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
      refine ⟨j, ?_, (original_fixed_locus_one_orbit
        sourceGenus quotientGenus hupper hRH j x).mp hj⟩
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
      (branch_values_iff sourceGenus quotientGenus hupper hRH i _).mpr
        ⟨j.val,j.property,rfl⟩⟩)
    ⟨by
      intro j k he
      apply Subtype.ext
      apply displayed_injective
      apply Subtype.ext
      exact congrArg Subtype.val he,
    by
      intro q
      obtain ⟨j,hj,he⟩ := (branch_values_iff sourceGenus quotientGenus hupper hRH i q.val).mp q.property
      refine ⟨⟨j,hj⟩,?_⟩
      apply Subtype.ext
      exact he.symm⟩

include hupper hRH in
theorem exactly_four_actual_branch_values (i : Fin 4) :
    Nat.card (CharacterBranchValues i) = 4 := by
  rw [← Nat.card_congr (branchEnumeration sourceGenus quotientGenus hupper hRH i),
    Nat.card_eq_fintype_card]
  exact visible_labels_card i

/-- All four omitted labels remain unramified in their corresponding
intermediate quotient, although they ARE ramified in the full sixteen cover. -/
theorem omitted_fiber_two (i : Fin 4) :
    Nat.card {y : CharacterBase i // toMaximal i y =
      PELOriginalMaximalQuotient318.projection (originalPoint (omitted i))} = 2 := by
  rw [branch_fiber_card i (omitted i) _ (original_label_fixes _),
    if_pos ((omitted_label i (omitted i)).mpr rfl)]
end PELOriginalCharacterBranches318
