module
public import PELOriginalAdjacentTransitionContrast318
public import PELOriginalHalfPlaneSheetTopology318
public section
noncomputable section
namespace PELOriginalAllBranchTransitions318
open Set Filter
open scoped Topology OnePoint
open PELOriginalRealBranchIntervals318 PELOriginalFourBranchCoordinate318
open PELOriginalRealBranchParameters318 PELOriginalAdjacentTransitionContrast318
open PELOriginalNormalizedDoubleCover318
variable {i:Fin 4} (O:Ordering i)

@[expose] def center : Fin 3→ℝ:=![O.lo,O.mid,O.hi]
@[expose] def leftIndex (j:Fin 3) : Fin 4:=⟨j.val,by omega⟩
@[expose] def rightIndex (j:Fin 3) : Fin 4:=⟨j.val+1,by omega⟩
lemma center_values (j:Fin 3) : O.center j=0 ∨ O.center j=1 ∨ O.center j=(branchParameter i).re := by
  apply (O.values _).mp
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
lemma left_interval_near (j:Fin 3) :
    ∀ᶠ x in 𝓝[<] (O.center j),x∈(O.interval (leftIndex j)).carrier := by
  fin_cases j
  · exact self_mem_nhdsWithin
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds O.lo_lt_mid).filter_mono nhdsWithin_le_nhds] with x hx hl
    exact ⟨hl,hx⟩
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds O.mid_lt_hi).filter_mono nhdsWithin_le_nhds] with x hx hl
    exact ⟨hl,hx⟩
lemma right_interval_near (j:Fin 3) :
    ∀ᶠ x in 𝓝[>] (O.center j),x∈(O.interval (rightIndex j)).carrier := by
  fin_cases j
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds O.lo_lt_mid).filter_mono nhdsWithin_le_nhds] with x hx hu
    exact ⟨hx,hu⟩
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds O.mid_lt_hi).filter_mono nhdsWithin_le_nhds] with x hx hu
    exact ⟨hx,hu⟩
  · exact self_mem_nhdsWithin

/-- Actual source branch points and all adjacent interval hypotheses are
PRODUCED for each of the three ordered original finite branch values. -/
theorem actual_adjacent_contrast (i:Fin 4) (j:Fin 3) :
    ∃e:PELOriginalGlobalHalfPlaneSheets318.BaseFiber i true,
      actualTransition i (leftIndex j) e≠actualTransition i (rightIndex j) e := by
  let O:=ordering i
  let a:=O.center j
  obtain ⟨p,hp⟩:=PELOriginalNormalizedDoubleCover318.surjective i (a:ℂ)
  have hb:(a:ℂ)=0 ∨ (a:ℂ)=1 ∨ (a:ℂ)=branchParameter i:=by
    rcases O.center_values j with h|h|h
    · exact Or.inl (by change ((O.center j:ℝ):ℂ)=0;rw [h];rfl)
    · exact Or.inr (Or.inl (by change ((O.center j:ℝ):ℂ)=1;rw [h];rfl))
    · exact Or.inr (Or.inr (by change ((O.center j:ℝ):ℂ)=branchParameter i
                              rw [h,←branchParameter_eq_real]))
  exact adjacent_contrast p a hp hb (O.interval (leftIndex j)) (O.interval (rightIndex j))
    (O.left_interval_near j) (O.right_interval_near j)

/-- Two permutations of a two-element set that differ anywhere differ by
the nontrivial swap EVERYWHERE. This is pure finite combinatorics after
the actual geometric crossing has supplied the mismatch. -/
lemma bool_flip (P Q:Equiv.Perm Bool) (h:∃b,P b≠Q b) : ∀b,Q b= !(P b) := by
  have hP:P false≠P true:=fun he=>Bool.false_ne_true (P.injective he)
  have hQ:Q false≠Q true:=fun he=>Bool.false_ne_true (Q.injective he)
  obtain ⟨b,hb⟩:=h
  intro c
  cases b <;> cases c <;> cases hp0:P false <;> cases hp1:P true <;>
    cases hq0:Q false <;> cases hq1:Q true <;> simp_all

/-- Original transitions in the SAME one-time Bool labelings already
used for the actual source-to-target halfplane comparison. -/
@[expose] def permutation (i:Fin 4) (j:Fin 4) : Equiv.Perm Bool:=
  (PELOriginalHalfPlaneSheetTopology318.enumeration i true).trans
    ((actualTransition i j).trans (PELOriginalHalfPlaneSheetTopology318.enumeration i false).symm)

/-- Across EACH of the three actual finite branches the original source
transition is exactly toggled. The four real interval matchings therefore
alternate; no sign-switch or monodromy input remains in this theorem. -/
theorem all_adjacent_flips (i:Fin 4) (j:Fin 3) (b:Bool) :
    permutation i (rightIndex j) b= !(permutation i (leftIndex j) b) := by
  apply bool_flip (permutation i (leftIndex j)) (permutation i (rightIndex j)) _ b
  obtain ⟨e,he⟩:=actual_adjacent_contrast i j
  let b:Bool:=(PELOriginalHalfPlaneSheetTopology318.enumeration i true).symm e
  refine ⟨b,?_⟩
  intro hh
  apply he
  apply (PELOriginalHalfPlaneSheetTopology318.enumeration i false).symm.injective
  simpa only [permutation,Equiv.trans_apply,b,Equiv.apply_symm_apply] using hh
end PELOriginalAllBranchTransitions318
