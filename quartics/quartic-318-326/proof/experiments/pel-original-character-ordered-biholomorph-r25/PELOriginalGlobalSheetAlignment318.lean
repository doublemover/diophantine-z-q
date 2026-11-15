module
public import LegendreAllBranchTransitions318
public section
noncomputable section
namespace PELOriginalGlobalSheetAlignment318
open PELOriginalAllBranchTransitions318

lemma equiv_not (E:Equiv.Perm Bool) (b:Bool) : E (!b)= !(E b) := by
  have hi:E false≠E true:=fun h=>Bool.false_ne_true (E.injective h)
  cases b <;> cases h0:E false <;> cases h1:E true <;> simp_all

/-- A SINGLE lower-sheet relabeling matches two four-interval transition
systems when each flips at each of the three actual finite branch points.
The upper labels remain unchanged. No per-interval choices are made. -/
@[expose] def alignment (P Q:Fin 4→Equiv.Perm Bool) : Equiv.Perm Bool:=
  (P 0).symm.trans (Q 0)
lemma alignment_zero (P Q:Fin 4→Equiv.Perm Bool) (b:Bool) : alignment P Q (P 0 b)=Q 0 b := by
  simp only [alignment,Equiv.trans_apply,Equiv.symm_apply_apply]

theorem alignment_all (P Q:Fin 4→Equiv.Perm Bool)
    (hP:∀j:Fin 3,∀b,P (rightIndex j) b= !(P (leftIndex j) b))
    (hQ:∀j:Fin 3,∀b,Q (rightIndex j) b= !(Q (leftIndex j) b)) :
    ∀j b,alignment P Q (P j b)=Q j b := by
  have h0:∀b,alignment P Q (P 0 b)=Q 0 b:=alignment_zero P Q
  have h1:∀b,alignment P Q (P 1 b)=Q 1 b:=by
    intro b
    rw [show P 1 b= !(P 0 b) from hP 0 b,equiv_not,h0,
      show Q 1 b= !(Q 0 b) from hQ 0 b]
  have h2:∀b,alignment P Q (P 2 b)=Q 2 b:=by
    intro b
    rw [show P 2 b= !(P 1 b) from hP 1 b,equiv_not,h1,
      show Q 2 b= !(Q 1 b) from hQ 1 b]
  have h3:∀b,alignment P Q (P 3 b)=Q 3 b:=by
    intro b
    rw [show P 3 b= !(P 2 b) from hP 2 b,equiv_not,h2,
      show Q 3 b= !(Q 2 b) from hQ 2 b]
  intro j b
  fin_cases j
  · exact h0 b
  · exact h1 b
  · exact h2 b
  · exact h3 b

/-- Constructed once from the SAME actual original source and actual
Legendre target transition systems already used in the two halfplane
comparisons. This is an explicit pairing, not uniqueness of a cover
inferred merely from its branch set or degree. -/
@[expose] def lowerAlignment (i:Fin 4) : Equiv.Perm Bool:=
  alignment (PELOriginalAllBranchTransitions318.permutation i)
    (LegendreAllBranchTransitions318.permutation i)

/-- Every real interval now respects the SAME chosen lower pairing.
Together with the existing actual strip continuations, this is the
compatibility needed to glue the halfplane comparisons across ALL seams. -/
theorem all_original_target_transitions (i:Fin 4) (j:Fin 4) (b:Bool) :
    lowerAlignment i (PELOriginalAllBranchTransitions318.permutation i j b)=
      LegendreAllBranchTransitions318.permutation i j b :=
  alignment_all _ _ (PELOriginalAllBranchTransitions318.all_adjacent_flips i)
    (LegendreAllBranchTransitions318.all_adjacent_flips i) j b
end PELOriginalGlobalSheetAlignment318
