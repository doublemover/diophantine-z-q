module
public import PELOriginalDirectBranchOrbits318
public import PELOriginalFiniteRamification318
public section
noncomputable section
namespace PELOriginalDirectBranchEnumeration318
open PELUnlevelledComplexBase318 PELOriginalLabeledFixedOrbits318
open PELOriginalBranchLabels318 PELStabilizerLocusInvariant318
open PELOriginalFiniteRamification318 PELOriginalDirectBranchOrbits318
set_option maxHeartbeats 2400000

/-- The FIVE original displayed branch values now exhaust the entire
actual branch image by direct original-normalizer classification. -/
theorem displayed_surjective : Function.Surjective displayed := by
  rintro ⟨q,hq⟩
  obtain ⟨x,hx,hxq⟩ := hq
  obtain ⟨v,hv,hfixed⟩ := hx
  obtain ⟨i,g,hg⟩ := every_branch_original_orbit x v hv hfixed
  refine ⟨i,Subtype.ext ?_⟩
  change PELOriginalMaximalQuotient318.projection (originalPoint i)=q
  have hp : PELOriginalMaximalQuotient318.projection x=
      PELOriginalMaximalQuotient318.projection (originalPoint i) :=
    (PELOriginalMaximalQuotient318.projection_eq_iff _ _).mpr ⟨g,hg⟩
  exact hp.symm.trans hxq

theorem displayed_bijective : Function.Bijective displayed :=
  ⟨displayed_injective,displayed_surjective⟩

@[expose] def branchEnumeration : Fin 5 ≃ BranchValues :=
  Equiv.ofBijective displayed displayed_bijective

/-- Whole original source ramification count, not the degree-six j-map
ramification divisor and not a selected five-point subset. -/
theorem actual_branch_and_ramification_counts :
    Fintype.card BranchValues=5 ∧ Fintype.card Ramification=40 := by
  have hb : Fintype.card BranchValues=5 := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr branchEnumeration).symm
  exact ⟨hb,by rw [total_ramification,hb]⟩

/-- Same-label fixed-locus classification, with the exact interface of
the old genus/RH consumer but neither of those inputs. -/
theorem original_fixed_locus_one_orbit (i : Fin 5) (x : UnlevelledBase) :
    x∈fixedLocus i ↔ PELOriginalMaximalQuotient318.projection x=
      PELOriginalMaximalQuotient318.projection (originalPoint i) := by
  constructor
  · intro hx
    have hb : PELOriginalMaximalQuotient318.projection x∈branchImage :=
      (branch_image_iff x).mpr ((original_locus_union x).mpr ⟨i,hx⟩)
    obtain ⟨j,hj⟩ := displayed_surjective ⟨_,hb⟩
    have he := congrArg Subtype.val hj
    obtain ⟨g,hg⟩ := (PELOriginalMaximalQuotient318.projection_eq_iff
      (originalPoint j) x).mp he
    have hi : originalPoint j∈fixedLocus i := by
      change Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) • originalPoint j=originalPoint j
      rw [←hg,action_commute,hx]
    have hij := fixed_locus_index_unique i j (originalPoint j) hi (original_label_fixes j)
    subst j
    exact he.symm
  · intro he
    obtain ⟨g,hg⟩ := (PELOriginalMaximalQuotient318.projection_eq_iff x (originalPoint i)).mp he
    change Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) • x=x
    rw [←hg,action_commute,original_label_fixes]
end PELOriginalDirectBranchEnumeration318
