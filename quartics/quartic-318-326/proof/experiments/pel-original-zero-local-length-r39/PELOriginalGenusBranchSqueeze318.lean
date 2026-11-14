module
public import FiveOrbitGenusSqueeze318
public import PELOriginalFiniteRamification318
public section
noncomputable section
namespace PELOriginalGenusBranchSqueeze318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalBranchLabels318 PELOriginalLabeledFixedOrbits318
open PELStabilizerLocusInvariant318 PELOriginalFiniteRamification318

/-- Source-specific squeeze on the SAME compact original quotient and its
actual finite full branch locus. Only the geometric genus upper bound and
Riemann--Hurwitz identity remain supplied; genus five is not assumed. -/
theorem original_genus_and_branches (sourceGenus quotientGenus : ℕ)
    (hupper : sourceGenus ≤ 5)
    (hRH : 2 * (sourceGenus : ℤ) - 2 =
      16 * (2 * (quotientGenus : ℤ) - 2) + (Fintype.card Ramification : ℤ)) :
    sourceGenus = 5 ∧ quotientGenus = 0 ∧ Fintype.card Ramification = 40 ∧
      Fintype.card BranchValues = 5 :=
  FiveOrbitGenusSqueeze318.numerical sourceGenus quotientGenus _ _ hupper
    at_least_five total_ramification hRH

theorem original_displayed_bijective (sourceGenus quotientGenus : ℕ)
    (hupper : sourceGenus ≤ 5)
    (hRH : 2 * (sourceGenus : ℤ) - 2 =
      16 * (2 * (quotientGenus : ℤ) - 2) + (Fintype.card Ramification : ℤ)) :
    Function.Bijective displayed := by
  have hc := (original_genus_and_branches sourceGenus quotientGenus hupper hRH).2.2.2
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨displayed_injective, by simpa only [Fintype.card_fin] using hc.symm⟩

/-- Every point of each ORIGINAL labeled fixed locus belongs to the orbit
of its very own displayed point. This derives same-label orbit uniqueness,
not just the number of branch fibers. -/
theorem original_fixed_locus_one_orbit (sourceGenus quotientGenus : ℕ)
    (hupper : sourceGenus ≤ 5)
    (hRH : 2 * (sourceGenus : ℤ) - 2 =
      16 * (2 * (quotientGenus : ℤ) - 2) + (Fintype.card Ramification : ℤ))
    (i : Fin 5) (x : UnlevelledBase) :
    x ∈ fixedLocus i ↔ PELOriginalMaximalQuotient318.projection x =
      PELOriginalMaximalQuotient318.projection (originalPoint i) := by
  constructor
  · intro hx
    have hb : PELOriginalMaximalQuotient318.projection x ∈ branchImage :=
      (branch_image_iff x).mpr ((original_locus_union x).mpr ⟨i, hx⟩)
    obtain ⟨j, hj⟩ := (original_displayed_bijective sourceGenus quotientGenus hupper hRH).2 ⟨_, hb⟩
    have he := congrArg Subtype.val hj
    obtain ⟨g, hg⟩ := (PELOriginalMaximalQuotient318.projection_eq_iff
      (originalPoint j) x).mp he
    have hi : originalPoint j ∈ fixedLocus i := by
      change Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) • originalPoint j = originalPoint j
      rw [← hg, action_commute, hx]
    have hij := fixed_locus_index_unique i j (originalPoint j) hi (original_label_fixes j)
    subst j
    exact he.symm
  · intro he
    obtain ⟨g, hg⟩ := (PELOriginalMaximalQuotient318.projection_eq_iff
      x (originalPoint i)).mp he
    change Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) • x = x
    rw [← hg, action_commute, original_label_fixes]
end PELOriginalGenusBranchSqueeze318
