module
public import PELOriginalRealStripCover318
public section
noncomputable section
namespace PELOriginalRealBranchIntervals318
open Set
open PELOriginalFourBranchCoordinate318 PELOriginalRealBranchParameters318
open PELOriginalRealStripCover318

/-- Actual ordered positions of the three finite branch values. The
original cross-ratio is retained in all three possible order cases. -/
structure Ordering (i:Fin 4) where
  lo:ℝ
  mid:ℝ
  hi:ℝ
  lo_lt_mid:lo<mid
  mid_lt_hi:mid<hi
  values:∀x:ℝ,(x=lo ∨ x=mid ∨ x=hi) ↔ (x=0 ∨ x=1 ∨ x=(branchParameter i).re)

@[expose] def ordering (i:Fin 4) : Ordering i := by
  let l:ℝ:=(branchParameter i).re
  have h0:l≠0:=(realParameter_nonexceptional i).1
  have h1:l≠1:=(realParameter_nonexceptional i).2
  by_cases hn:l<0
  · exact ⟨l,0,1,hn,by norm_num,by intro x;dsimp [l];aesop⟩
  · have hp:0<l:=lt_of_le_of_ne (le_of_not_gt hn) h0.symm
    by_cases hl:l<1
    · exact ⟨0,l,1,hp,hl,by intro x;dsimp [l];aesop⟩
    · have hg:1<l:=lt_of_le_of_ne (le_of_not_gt hl) h1.symm
      exact ⟨0,1,l,by norm_num,hg,by intro x;rfl⟩

variable {i:Fin 4} (O:Ordering i)
@[expose] def gap : Fin 4→Set ℝ:=![Iio O.lo,Ioo O.lo O.mid,Ioo O.mid O.hi,Ioi O.hi]
@[expose] def witness : Fin 4→ℝ:=![O.lo-1,(O.lo+O.mid)/2,(O.mid+O.hi)/2,O.hi+1]
lemma gap_open (j:Fin 4) : IsOpen (O.gap j) := by
  fin_cases j
  · exact isOpen_Iio
  · exact isOpen_Ioo
  · exact isOpen_Ioo
  · exact isOpen_Ioi
lemma gap_convex (j:Fin 4) : Convex ℝ (O.gap j) := by
  fin_cases j
  · exact convex_Iio _
  · exact convex_Ioo _ _
  · exact convex_Ioo _ _
  · exact convex_Ioi _
lemma witness_mem (j:Fin 4) : O.witness j∈O.gap j := by
  have h0:=O.lo_lt_mid
  have h1:=O.mid_lt_hi
  fin_cases j
  · change O.lo-1<O.lo
    linarith
  · change O.lo<(O.lo+O.mid)/2 ∧ (O.lo+O.mid)/2<O.mid
    constructor <;> linarith
  · change O.mid<(O.mid+O.hi)/2 ∧ (O.mid+O.hi)/2<O.hi
    constructor <;> linarith
  · change O.hi<O.hi+1
    linarith
lemma gap_avoids (j:Fin 4) (x:ℝ) (hx:x=O.lo ∨ x=O.mid ∨ x=O.hi) : x∉O.gap j := by
  have h0:=O.lo_lt_mid
  have h1:=O.mid_lt_hi
  intro hm
  fin_cases j <;> simp [gap] at hm <;> rcases hx with rfl|rfl|rfl <;> linarith

/-- These are the FOUR actual entire complementary real intervals, not
unspecified local neighborhoods or an assumed branch ordering. -/
@[expose] def interval (j:Fin 4) : Interval i where
  carrier:=O.gap j
  isOpen:=O.gap_open j
  convex:=O.gap_convex j
  point:=O.witness j
  point_mem:=O.witness_mem j
  zero_not:=O.gap_avoids j 0 ((O.values 0).mpr (Or.inl rfl))
  one_not:=O.gap_avoids j 1 ((O.values 1).mpr (Or.inr (Or.inl rfl)))
  parameter_not:=O.gap_avoids j (branchParameter i).re ((O.values _).mpr (Or.inr (Or.inr rfl)))

lemma gaps_cover (x:ℝ) (hx:¬(x=0 ∨ x=1 ∨ x=(branchParameter i).re)) :
    ∃j:Fin 4,x∈O.gap j := by
  have hn:¬(x=O.lo ∨ x=O.mid ∨ x=O.hi):=fun h=>hx ((O.values x).mp h)
  have h0:x≠O.lo:=fun h=>hn (Or.inl h)
  have h1:x≠O.mid:=fun h=>hn (Or.inr (Or.inl h))
  have h2:x≠O.hi:=fun h=>hn (Or.inr (Or.inr h))
  by_cases h:x<O.lo
  · exact ⟨0,h⟩
  · have h':O.lo<x:=lt_of_le_of_ne (le_of_not_gt h) h0.symm
    by_cases h:x<O.mid
    · exact ⟨1,⟨h',h⟩⟩
    · have h'':O.mid<x:=lt_of_le_of_ne (le_of_not_gt h) h1.symm
      by_cases h:x<O.hi
      · exact ⟨2,⟨h'',h⟩⟩
      · exact ⟨3,lt_of_le_of_ne (le_of_not_gt h) h2.symm⟩

/-- A fixed transition on each actual component of the real unbranched
locus, constructed from the SAME original curve's global strip lifts. -/
@[expose] def actualTransition (i:Fin 4) (j:Fin 4) := ((ordering i).interval j).transition

theorem actual_transition_lift (i:Fin 4) (j:Fin 4)
    (e:PELOriginalGlobalHalfPlaneSheets318.BaseFiber i true) :
    ∃F:C(((ordering i).interval j).Domain,PELOriginalCharacterQuotient318.CharacterBase i),
      (∀z:((ordering i).interval j).HalfDomain true,
        PELOriginalGlobalHalfPlaneSheets318.sheet i true e (((ordering i).interval j).toHalf true z)=
          F (((ordering i).interval j).toStrip true z)) ∧
      (∀z:((ordering i).interval j).HalfDomain false,
        PELOriginalGlobalHalfPlaneSheets318.sheet i false (actualTransition i j e)
          (((ordering i).interval j).toHalf false z)=F (((ordering i).interval j).toStrip false z)) :=
  ((ordering i).interval j).transition_lift e
end PELOriginalRealBranchIntervals318
