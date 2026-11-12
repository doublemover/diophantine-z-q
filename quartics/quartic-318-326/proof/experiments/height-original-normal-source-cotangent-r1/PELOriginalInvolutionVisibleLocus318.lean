module
public import PELOriginalInvolutionMaximalFibers318
public section
noncomputable section
namespace PELOriginalInvolutionVisibleLocus318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalInvolutionTower318 PELOriginalInvolutionMaximalFibers318
open PELOriginalCharacterBranches318 (CharacterBranchValues)
open PELOriginalBranchLabels318 PELOriginalLabeledFixedOrbits318
set_option maxHeartbeats 2400000

/-- The actual entire inverse image of the four visible branch values in
the degree-eight involution quotient. Local ramification is supplied separately. -/
abbrev VisibleLocus (i : Fin 4) :=
  {y : InvolutionBase i // toOriginalMaximal i y∈CharacterBranchValues i}

instance visibleBranchFinite (i : Fin 4) : Finite (CharacterBranchValues i) :=
  Finite.of_equiv _ (PELOriginalDirectCharacterBranches318.branchEnumeration i)

@[expose] def visibleDecomposition (i : Fin 4) :
    VisibleLocus i ≃ Σ q : CharacterBranchValues i,InvolutionFiber i q.val where
  toFun y := ⟨⟨toOriginalMaximal i y.val,y.property⟩,⟨y.val,rfl⟩⟩
  invFun y := ⟨y.2.val,y.2.property.symm ▸ y.1.property⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨q,hq⟩,⟨y,hy⟩⟩
    dsimp at hy
    subst q
    rfl

instance visibleFinite (i : Fin 4) : Finite (VisibleLocus i) :=
  Finite.of_equiv _ (visibleDecomposition i).symm

/-- Sixteen actual source points lie above the four visible branch values
of the degree-eight map, not four chosen points or an unrelated divisor. -/
theorem visible_locus_card (i : Fin 4) : Nat.card (VisibleLocus i)=16 := by
  classical
  letI : Fintype (VisibleLocus i) := Fintype.ofFinite _
  letI : Fintype (CharacterBranchValues i) := Fintype.ofFinite _
  letI (q : CharacterBranchValues i) : Fintype (InvolutionFiber i q.val) := Fintype.ofFinite _
  have h := Fintype.card_congr (visibleDecomposition i)
  rw [Fintype.card_sigma] at h
  have hf (q : CharacterBranchValues i) : Fintype.card (InvolutionFiber i q.val)=4 := by
    simpa only [Nat.card_eq_fintype_card,if_pos q.property] using actual_fiber_card i q.val
  simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul] at h
  have hb := PELOriginalDirectCharacterBranches318.exactly_four_actual_branch_values i
  rw [Nat.card_eq_fintype_card] at hb ⊢
  rw [hb] at h
  exact h

/-- Each original nontrivial inertia fixes exactly eight points of the
ORIGINAL curve, by actual same-label orbit classification and whole fibers. -/
theorem original_fixed_locus_card (j : Fin 5) : Nat.card (fixedLocus j)=8 := by
  have he : fixedLocus j={x : UnlevelledBase |
      PELOriginalMaximalQuotient318.projection x=
        PELOriginalMaximalQuotient318.projection (originalPoint j)} := by
    ext x
    exact PELOriginalDirectBranchEnumeration318.original_fixed_locus_one_orbit j x
  rw [he]
  have h := PELMaximalFiberCardinality318.original_fiber_card
    (PELOriginalMaximalQuotient318.projection (originalPoint j))
  rw [if_pos (PELOriginalFiniteRamification318.displayed j).property] at h
  exact h
end PELOriginalInvolutionVisibleLocus318
