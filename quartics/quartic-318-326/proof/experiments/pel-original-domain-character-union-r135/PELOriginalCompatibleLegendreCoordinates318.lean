module
public import PELOriginalOpenRealStripSheets318
public import PELOriginalGlobalSheetAlignment318
public section
noncomputable section
namespace PELOriginalCompatibleLegendreCoordinates318
open Set
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 PELOriginalRealBranchParameters318
open PELOriginalRealBranchIntervals318 PELOriginalRealStripCover318
open PELOriginalOpenRealStripSheets318 PELOriginalGlobalHalfPlaneSheets318
open PELOriginalHalfPlaneSheetTopology318 PELOriginalGlobalSheetAlignment318
open LegendreHalfPlaneAnalyticSheets318 LegendreAllBranchTransitions318

/-- The original labels are retained upstairs. Only the ONE geometrically
constructed lower pairing is changed; no choices depend on a real interval. -/
@[expose] def targetLabel (i:Fin 4) (upper b:Bool) : Bool:=
  if upper then b else lowerAlignment i b
@[expose] def halfValue (i:Fin 4) (upper b:Bool) (z:ℂ) : ℂ:=
  signed (targetLabel i upper b) (root (branchParameter i) (branchParameter_im_zero i) upper z)
lemma halfValue_analytic (i:Fin 4) (upper b:Bool) :
    AnalyticOnNhd ℂ (halfValue i upper b) (domain upper) := by
  intro z hz
  unfold halfValue signed
  split
  · exact root_analytic _ _ upper z hz
  · exact (root_analytic _ _ upper z hz).neg
lemma halfValue_square (i:Fin 4) (upper b:Bool) (z:ℂ) :
    halfValue i upper b z^2=polynomial (branchParameter i) z := by
  unfold halfValue signed
  split <;> simpa using root_square (branchParameter i) (branchParameter_im_zero i) upper z

/-- The SAME signed target continuation is selected on each whole strip.
Its two restrictions are the old global roots with the proved transition. -/
@[expose] def stripValue (i:Fin 4) (j:Fin 4) (b:Bool) (z:ℂ) : ℂ:=
  signed b (LegendreRealStripSheets318.halfSign ((ordering i).interval j) true*
    LegendreRealStripSheets318.stripRoot ((ordering i).interval j) z)
lemma stripValue_analytic (i:Fin 4) (j:Fin 4) (b:Bool) :
    AnalyticOnNhd ℂ (stripValue i j b) ((ordering i).interval j).Domain:=by
  intro z hz
  have hh:AnalyticAt ℂ (fun w=>LegendreRealStripSheets318.halfSign ((ordering i).interval j) true*
      LegendreRealStripSheets318.stripRoot ((ordering i).interval j) w) z:=
    analyticAt_const.mul (LegendreRealStripSheets318.stripRoot_analytic _ z hz)
  cases b
  · exact hh.neg
  · exact hh
lemma stripValue_square (i:Fin 4) (j:Fin 4) (b:Bool) (z:ℂ) :
    stripValue i j b z^2=polynomial (branchParameter i) z:=by
  cases b <;> simp [stripValue,signed,mul_pow,
    LegendreRealStripSheets318.halfSign_square,LegendreRealStripSheets318.stripRoot_square]
lemma stripValue_upper (i:Fin 4) (j:Fin 4) (b:Bool)
    (z:((ordering i).interval j).HalfDomain true) :
    stripValue i j b z.val=halfValue i true b z.val :=by
  unfold halfValue targetLabel
  rw [if_pos rfl,LegendreRealStripSheets318.halfSign_formula _ true z.val z.property]
  rfl
lemma stripValue_lower (i:Fin 4) (j:Fin 4) (b:Bool)
    (z:((ordering i).interval j).HalfDomain false) :
    stripValue i j b z.val=halfValue i false
      (PELOriginalAllBranchTransitions318.permutation i j b) z.val := by
  let J:Interval i:=(ordering i).interval j
  have he:LegendreRealStripSheets318.halfSign J true*LegendreRealStripSheets318.stripRoot J z.val=
      LegendreAllBranchTransitions318.sign i j*
        root (branchParameter i) (branchParameter_im_zero i) false z.val:=by
    rw [LegendreRealStripSheets318.halfSign_formula _ false z.val z.property]
    have hs:=LegendreRealStripSheets318.halfSign_square J false
    dsimp [LegendreAllBranchTransitions318.sign,LegendreRealStripSheets318.transitionSign]
    linear_combination -(LegendreRealStripSheets318.halfSign J true*
      LegendreRealStripSheets318.stripRoot J z.val)*hs
  change signed b (_*_)=_
  rw [he,signed_action]
  unfold halfValue targetLabel
  rw [if_neg Bool.false_ne_true,all_original_target_transitions]

/-- Actual source strip parametrization in the same one-time upper labels. -/
@[expose] def sourceStrip (i:Fin 4) (j:Fin 4) (b:Bool) :=
  stripSheet ((ordering i).interval j) (enumeration i true b)
@[expose] def sourceHalf (i:Fin 4) (upper b:Bool) :=
  PELOriginalGlobalHalfPlaneSheets318.sheet i upper (enumeration i upper b)

/-- At EVERY actual source overlap the target coordinates coincide.
This derives the lower label from the original whole-cover transition
and then consumes the global alignment, rather than assuming seam glue. -/
theorem strip_half_compatible (i:Fin 4) (j:Fin 4) (upper b c:Bool)
    (z:((ordering i).interval j).Domain) (w:Half upper)
    (he:sourceStrip i j b z=sourceHalf i upper c w) :
    stripValue i j b z.val=halfValue i upper c w.val := by
  let J:Interval i:=(ordering i).interval j
  have hcoord:z.val=w.val:=by
    have hh:=congrArg (normalizedMap i) he
    rw [show normalizedMap i (sourceStrip i j b z)=(z.val:OnePoint ℂ) from
      strip_projection J (enumeration i true b) z,
      PELOriginalGlobalHalfPlaneSheets318.sheet_projection] at hh
    exact OnePoint.coe_injective hh
  have hl:=overlap_label J upper (enumeration i true b) (enumeration i upper c) z w he
  let v:J.HalfDomain upper:=⟨z.val,z.property,hcoord.symm ▸ w.property⟩
  cases upper
  · have hc:c=PELOriginalAllBranchTransitions318.permutation i j b:=by
      apply (enumeration i false).injective
      simpa only [PELOriginalAllBranchTransitions318.permutation,
        Equiv.trans_apply,Equiv.apply_symm_apply,actualTransition,PELOriginalRealStripCover318.transition,J] using hl
    rw [hc,←hcoord]
    exact stripValue_lower i j b v
  · have hc:c=b:=by
      apply (enumeration i true).injective
      simpa only [Equiv.apply_symm_apply] using hl
    rw [hc,←hcoord]
    exact stripValue_upper i j b v
end PELOriginalCompatibleLegendreCoordinates318
