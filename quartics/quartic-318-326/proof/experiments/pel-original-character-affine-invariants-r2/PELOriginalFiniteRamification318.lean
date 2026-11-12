module
public import PELOriginalFiniteBranchImage318
public import PELMaximalFiberCardinality318
public section
noncomputable section
open scoped BigOperators
namespace PELOriginalFiniteRamification318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalBranchLabels318 PELStabilizerLocusInvariant318
open PELOriginalLabeledFixedOrbits318

abbrev BranchValues := branchImage
abbrev Ramification := nontrivialStabilizerLocus
abbrev Fiber (q : BranchValues) :=
  {x : UnlevelledBase // PELOriginalMaximalQuotient318.projection x = q.val}

instance branchValuesFintype : Fintype BranchValues :=
  PELOriginalFiniteBranchImage318.original_branch_image_finite.fintype
instance fiberFintype (q : BranchValues) : Fintype (Fiber q) :=
  (PELMaximalQuotientProper318.fiber_finite q.val).fintype

/-- Literal ramification points decompose into the ENTIRE actual fibers
over the actual branch image, using the original quotient projection. -/
@[expose] def fiberDecomposition : Ramification ≃ Σ q : BranchValues, Fiber q where
  toFun x := ⟨⟨PELOriginalMaximalQuotient318.projection x.val,
    (branch_image_iff x.val).mpr x.property⟩, ⟨x.val, rfl⟩⟩
  invFun x := ⟨x.2.val, (branch_image_iff x.2.val).mp (x.2.property.symm ▸ x.1.property)⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨q, hq⟩, ⟨x, hx⟩⟩
    dsimp at hx
    subst q
    rfl

instance ramificationFintype : Fintype Ramification :=
  Fintype.ofEquiv (Σ q : BranchValues, Fiber q) fiberDecomposition.symm

/-- All fibers over the actual branch image have eight points. -/
theorem fiber_card (q : BranchValues) : Fintype.card (Fiber q) = 8 := by
  have h := PELMaximalFiberCardinality318.original_fiber_card q.val
  rw [if_pos q.property] at h
  simpa only [Nat.card_eq_fintype_card] using h

/-- The whole original ramification count, not a selected subset of roots. -/
theorem total_ramification : Fintype.card Ramification = Fintype.card BranchValues * 8 := by
  have h := Fintype.card_congr fiberDecomposition
  rw [Fintype.card_sigma] at h
  simp_rw [fiber_card] at h
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using h

@[expose] def displayed (i : Fin 5) : BranchValues :=
  ⟨PELOriginalMaximalQuotient318.projection (originalPoint i),
    (branch_image_iff _).mpr ⟨InertiaLabels318.fiveLabels i,
      InertiaLabels318.five_labels_nonzero i, original_label_fixes i⟩⟩

/-- Distinctness is inherited from the actual full-normalizer orbit theorem. -/
theorem displayed_injective : Function.Injective displayed := by
  intro i j h
  have he := congrArg Subtype.val h
  obtain ⟨g, hg⟩ := (PELOriginalMaximalQuotient318.projection_eq_iff
    (originalPoint i) (originalPoint j)).mp he
  exact (distinct_labeled_orbits g j i hg).symm

theorem at_least_five : 5 ≤ Fintype.card BranchValues := by
  simpa using Fintype.card_le_of_injective displayed displayed_injective
end PELOriginalFiniteRamification318
