module
public import LegendreAdjacentTransitionFlip318
public import PELOriginalAllBranchTransitions318
public section
noncomputable section
namespace LegendreAllBranchTransitions318
open Set Filter
open scoped Topology
open PELOriginalFourBranchCoordinate318 PELOriginalRealBranchIntervals318
open PELOriginalAllBranchTransitions318 LegendreRealStripSheets318
open LegendreSimpleBranchCharts318

@[expose] def sign (i:Fin 4) (j:Fin 4) : ℂ:=transitionSign ((ordering i).interval j)
lemma sign_square (i:Fin 4) (j:Fin 4) : sign i j^2=1:=transitionSign_square _

/-- All geometric interval hypotheses are constructed for the three
sorted actual branch values, retaining the actual arbitrary parameter. -/
theorem all_sign_flips (i:Fin 4) (j:Fin 3) : sign i (rightIndex j)= -sign i (leftIndex j) := by
  let O:=ordering i
  obtain ⟨k,hk⟩:∃k:Fin 3,(branch (branchParameter i) k).re=O.center j:=by
    rcases O.center_values j with h|h|h
    · exact ⟨0,by simpa [branch] using h.symm⟩
    · exact ⟨1,by simpa [branch] using h.symm⟩
    · exact ⟨2,by simpa [branch] using h.symm⟩
  have hL:∀ᶠ x in 𝓝[<] (branch (branchParameter i) k).re,
      x∈(O.interval (leftIndex j)).carrier:=by rw [hk];exact O.left_interval_near j
  have hR:∀ᶠ x in 𝓝[>] (branch (branchParameter i) k).re,
      x∈(O.interval (rightIndex j)).carrier:=by rw [hk];exact O.right_interval_near j
  have hh:=LegendreAdjacentTransitionFlip318.adjacent_flip k
    (O.interval (leftIndex j)) (O.interval (rightIndex j)) hL hR
  change sign i (leftIndex j)= -sign i (rightIndex j) at hh
  linear_combination hh

@[expose] def toggle : Equiv.Perm Bool where
  toFun:=Bool.not
  invFun:=Bool.not
  left_inv b:=by cases b <;> rfl
  right_inv b:=by cases b <;> rfl
/-- Actual target transition in the SAME positive/negative sheet labels
used in the whole-halfplane target homeomorphism. -/
@[expose] def permutation (i:Fin 4) (j:Fin 4) : Equiv.Perm Bool:=
  if sign i j=1 then Equiv.refl Bool else toggle
lemma sign_cases (i:Fin 4) (j:Fin 4) : sign i j=1 ∨ sign i j= -1 :=
  sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa using sign_square i j)
lemma all_adjacent_flips (i:Fin 4) (j:Fin 3) (b:Bool) :
    permutation i (rightIndex j) b= !(permutation i (leftIndex j) b) := by
  have h:=all_sign_flips i j
  rcases sign_cases i (leftIndex j) with hs|hs
  · rw [hs] at h
    simp only [permutation,hs,h,if_pos rfl]
    norm_num [toggle]
  · rw [hs,neg_neg] at h
    simp only [permutation,hs,h,if_pos rfl]
    norm_num [toggle]
@[expose] def signed (b:Bool) (z:ℂ) : ℂ:=if b then z else -z

/-- The Bool permutation is proved to act on the ACTUAL target root
values, not just introduced as an abstract alternating label system. -/
lemma signed_action (i:Fin 4) (j:Fin 4) (b:Bool) (z:ℂ) :
    signed b (sign i j*z)=signed (permutation i j b) z := by
  rcases sign_cases i j with hs|hs <;> cases b <;>
    simp [signed,permutation,hs,toggle]

lemma actual_seam_matching (i:Fin 4) (j:Fin 4) (b:Bool) (a:ℝ) :
    signed b (LegendreRootArcMatching318.seamRoot ((ordering i).interval j) true a)=
      signed (permutation i j b)
        (LegendreRootArcMatching318.seamRoot ((ordering i).interval j) false a) := by
  rw [LegendreRootArcMatching318.seam_transition]
  exact signed_action i j b _

/-- Both ACTUAL signed global halfplane roots, with exactly this target
Bool transition, extend as one holomorphic function on the whole strip. -/
theorem actual_signed_continuation (i:Fin 4) (j:Fin 4) (b:Bool) :
    ∃F:ℂ→ℂ,AnalyticOnNhd ℂ F ((ordering i).interval j).Domain ∧
      (∀z,F z^2=LegendreHalfPlaneAnalyticSheets318.polynomial (branchParameter i) z) ∧
      (∀z∈((ordering i).interval j).HalfDomain true,F z=signed b
        (LegendreHalfPlaneAnalyticSheets318.root (branchParameter i)
          (PELOriginalRealBranchParameters318.branchParameter_im_zero i) true z)) ∧
      (∀z∈((ordering i).interval j).HalfDomain false,F z=signed (permutation i j b)
        (LegendreHalfPlaneAnalyticSheets318.root (branchParameter i)
          (PELOriginalRealBranchParameters318.branchParameter_im_zero i) false z)) := by
  obtain ⟨F,hF,hsq,hupper,hlower⟩:=analytic_continuation ((ordering i).interval j)
  refine ⟨fun z=>signed b (F z),?_,?_,?_,?_⟩
  · intro z hz
    cases b
    · exact (hF z hz).neg
    · exact hF z hz
  · intro z
    cases b <;> simpa [signed] using hsq z
  · intro z hz
    rw [hupper z hz]
  · intro z hz
    rw [hlower z hz]
    exact signed_action i j b _
end LegendreAllBranchTransitions318
