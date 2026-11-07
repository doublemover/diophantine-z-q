module
public import SourceScalarHeight318
public import SourceDetectorScales318
public import SourceSeparation318
public import SourceContactContracts318
public import LucasGrowth318
public section
noncomputable section
namespace SourceHeightComparisons318
open CircuitReplay Raw318FinalReplay RawProductHeight318 SourceLabelData318
open SourceContactDivisibility318 SourceContactContracts318 HeightSeparation318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma high_target_cast (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w)
    (labels:Labels w source) :
    (highTarget labels:ℝ)=lucasResidual (rootLabel labels 1) (rootLabel labels 2) (rootLabel labels 3) := by
  simp only [highTarget,lucasResidual]
  push_cast
  rfl

lemma high_comparison (hFive:ContactHeight318.FiveContact49Height)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (hne:lucasResidual (rootLabel labels 1) (rootLabel labels 2) (rootLabel labels 3)≠0) :
    (maxIndex (rootLabel labels):ℝ)^2-6<7*heightConstant*
      |lucasResidual (rootLabel labels 1) (rootLabel labels 2) (rootLabel labels 3)|^((49:ℝ)/104) := by
  have hN:highTarget labels≠0 := by
    intro hz
    apply hne
    rw [←high_target_cast w source labels,hz,Int.cast_zero]
  have hh:=SourceDetectorScales318.source_index_height_comparison _ w source
    (rootLabel labels) labels.roots labels.odd heightConstant heightConstant_ge_one
    (highTarget labels) hN 13
    (by convert source_high_height0 hFive w source labels hN using 1 <;> norm_num)
    (by convert source_high_height1 hFive w source labels hN using 1 <;> norm_num)
    (by convert source_high_height2 hFive w source labels hN using 1 <;> norm_num)
  simpa only [high_target_cast w source labels,Nat.cast_ofNat,show (8:ℝ)*13=104 by norm_num] using hh

/-- Bind the optimized source beta coordinate to the literal input polynomial. -/
lemma source_beta (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) :
    ContactLeafData318.beta w=3723*(2*w 0+1)^2 := by
  have h79:r79 ((3:ℚ)^65536) w=0 := source _
    (List.getElem_mem (l:=stage0 ((3:ℚ)^65536)) (n:=79)
      (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r79] at h79
  dsimp only [ContactLeafData318.beta]
  linear_combination 14892*h79

lemma low_target_formula (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w)
    (labels:Labels w source) :
    lowTarget w labels=3723*(2*w 0+1)^2-(rootLabel labels 0:ℚ) := by
  rw [lowTarget,source_beta w source]

lemma low_comparison (hFive:ContactHeight318.FiveContact49Height)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) (labels:Labels w source)
    (hne:3723*(2*w 0+1)^2≠(rootLabel labels 0:ℚ)) :
    (maxIndex (rootLabel labels):ℝ)^2-6<7*heightConstant*
      (((3723*(2*w 0+1)^2-(rootLabel labels 0:ℚ)).num.natAbs:ℝ)^((49:ℝ)/32)) := by
  have hN:(lowTarget w labels).num≠0 := by
    intro hz
    have hh:lowTarget w labels=0 := Rat.num_eq_zero.mp hz
    apply hne
    rw [low_target_formula w source labels] at hh
    exact sub_eq_zero.mp hh
  have hh:=SourceDetectorScales318.source_index_height_comparison _ w source
    (rootLabel labels) labels.roots labels.odd heightConstant heightConstant_ge_one
    (lowTarget w labels).num hN 4
    (by convert source_low_height0 hFive w source labels hN using 1 <;> norm_num)
    (by convert source_low_height1 hFive w source labels hN using 1 <;> norm_num)
    (by convert source_low_height2 hFive w source labels hN using 1 <;> norm_num)
  rw [low_target_formula w source labels] at hh
  simpa only [Nat.cast_natAbs,Int.cast_abs,Nat.cast_ofNat,
    show (8:ℝ)*4=32 by norm_num] using hh

/-- Every literal arithmetic and analytic comparison except the named global
five-contact49/8 producer is discharged for the same actual source labels. -/
theorem source_integer_input (hFive:ContactHeight318.FiveContact49Height)
    (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) :
    ∃x:ℤ,(x:ℚ)=w 0 := by
  obtain ⟨labels⟩:=labels_exist w source
  have hc0:=RawOddAnchorPoints318.scalar_label_nonzero w labels.c labels.scalar
  have hanchor:=SourceSeparation318.scalar_anchor_size labels.c hc0 labels.anchor_divides
  have horient:=SourceSeparation318.scalar_orientation (rootLabel labels) labels.c labels.orientation
  have hc4:4<(labels.c.natAbs:ℝ) := by
    have hh:(4:ℝ)≤2^49151 := by
      calc
        (4:ℝ)=2^2 := by norm_num
        _≤2^49151 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    exact hh.trans_lt labels.anchor_bound
  have hB:=three_le_maxIndex_of_scalar_bound (rootLabel labels) labels.c labels.orientation hc4
  have hz:rootLabel labels 3≠0 :=
    RawOddAnchorPoints318.root_labels_nonzero w (rootLabel labels) labels.roots 3
  exact LucasSequence318.integer_input_from_three_height_comparisons (w 0)
    (rootLabel labels 0) (rootLabel labels 1) (rootLabel labels 2) (rootLabel labels 3)
    (maxIndex (rootLabel labels):ℝ) (labels.c.natAbs:ℝ) (labels.odd 0) hz hB
    (label_abs_le_maxIndex (rootLabel labels) 0) (label_abs_le_maxIndex (rootLabel labels) 1)
    (label_abs_le_maxIndex (rootLabel labels) 2) (label_abs_le_maxIndex (rootLabel labels) 3)
    horient hanchor (high_comparison hFive w source labels)
    (SourceScalarHeight318.labeled_scalar_comparison hFive w source labels)
    (low_comparison hFive w source labels)

#print axioms high_target_cast
#print axioms high_comparison
#print axioms source_beta
#print axioms low_target_formula
#print axioms low_comparison
#print axioms source_integer_input
end SourceHeightComparisons318
