module
public import LegendreRootArcMatching318
public import LegendreFiniteCrossingLifts318
public import PELOriginalAdjacentTransitionContrast318
public section
noncomputable section
namespace LegendreAdjacentTransitionFlip318
open Set Filter
open scoped Topology
open PELOriginalFourBranchCoordinate318 PELOriginalRealBranchParameters318
open PELOriginalRealStripCover318 LegendreRealStripSheets318
open LegendreSimpleBranchCharts318 SimpleBranchCrossingPaths318
open LegendreRootArcMatching318
variable {i:Fin 4}
set_option maxHeartbeats 1200000

/-- The transitions of the ACTUAL already chosen target halfplane roots
change sign across EACH original simple finite branch. Both endpoint
identifications are obtained by limits of genuine whole-strip roots and
explicit target crossing lifts, not assumed monodromy data. -/
theorem adjacent_flip (j:Fin 3) (L R:Interval i)
    (hL:∀ᶠ x in 𝓝[<] (branch (branchParameter i) j).re,x∈L.carrier)
    (hR:∀ᶠ x in 𝓝[>] (branch (branchParameter i) j).re,x∈R.carrier) :
    transitionSign L= -transitionSign R := by
  let l:=branchParameter i
  have h0:l≠0:=(branchParameter_nonexceptional i).1
  have h1:l≠1:=(branchParameter_nonexceptional i).2
  let a:ℝ:=(branch l j).re
  have hsmall:∀ᶠ s in 𝓝 (0:ℝ),0<s → a-s^2∈L.carrier ∧ a+s^2∈R.carrier:=
    PELOriginalAdjacentTransitionContrast318.small_offsets a L R hL hR
  obtain ⟨δ,hδ,hball⟩:=Metric.mem_nhds_iff.mp hsmall
  obtain ⟨s,hs,hsδ,hcont,hcontAt,hn⟩:=LegendreFiniteCrossingLifts318.exists_crossing l h0 h1 j δ hδ
  have hends:a-s^2∈L.carrier ∧ a+s^2∈R.carrier:=by
    apply hball
    · rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hs]
      exact hsδ
    · exact hs
  let Y:Bool→ℝ→ℂ:=fun upper=>LegendreFiniteCrossingLifts318.lift l h0 h1 j upper s
  have hy:∀upper t,t∈Interior,Y upper t^2=LegendreHalfPlaneAnalyticSheets318.polynomial l (baseArc a upper s t):=
    fun upper t _=>LegendreFiniteCrossingLifts318.lift_square l h0 h1 j (branchParameter_im_zero i) upper s t
  obtain ⟨sp,hsp,he⟩:=one_root i true (baseArc a true s) (Y true)
    (baseArc_continuous a true s).continuousOn ((hcont true).mono Ioo_subset_Icc_self)
    (fun t ht=>interior_halfplane a true s t hs ht) (hy true)
  obtain ⟨sm,hsm,hf⟩:=one_root i false (baseArc a false s) (Y false)
    (baseArc_continuous a false s).continuousOn ((hcont false).mono Ioo_subset_Icc_self)
    (fun t ht=>interior_halfplane a false s t hs ht) (hy false)
  have hnear0:∀ᶠ t in 𝓝[>] (0:ℝ),t∈Interior:=by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht'
    exact ⟨ht,ht'⟩
  have hnear1:∀ᶠ t in 𝓝[<] (1:ℝ),t∈Interior:=by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht'
    exact ⟨ht',ht⟩
  have hRup:seamRoot R true (a+s^2)=sp*Y true 0:=
    endpoint R true (baseArc a true s) (Y true) sp
      (fun t ht=>interior_halfplane a true s t hs ht) he 0 (a+s^2) hends.2
      (baseArc_start a true s) (baseArc_continuous a true s).continuousAt
      (hcontAt true 0 ⟨le_rfl,by norm_num⟩) (𝓝[>] 0)
      (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds) hnear0
  have hRlo:seamRoot R false (a+s^2)=sm*Y false 0:=
    endpoint R false (baseArc a false s) (Y false) sm
      (fun t ht=>interior_halfplane a false s t hs ht) hf 0 (a+s^2) hends.2
      (baseArc_start a false s) (baseArc_continuous a false s).continuousAt
      (hcontAt false 0 ⟨le_rfl,by norm_num⟩) (𝓝[>] 0)
      (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds) hnear0
  have hLup:seamRoot L true (a-s^2)=sp*Y true 1:=
    endpoint L true (baseArc a true s) (Y true) sp
      (fun t ht=>interior_halfplane a true s t hs ht) he 1 (a-s^2) hends.1
      (baseArc_end a true s) (baseArc_continuous a true s).continuousAt
      (hcontAt true 1 ⟨by norm_num,le_rfl⟩) (𝓝[<] 1)
      (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds) hnear1
  have hLlo:seamRoot L false (a-s^2)=sm*Y false 1:=
    endpoint L false (baseArc a false s) (Y false) sm
      (fun t ht=>interior_halfplane a false s t hs ht) hf 1 (a-s^2) hends.1
      (baseArc_end a false s) (baseArc_continuous a false s).continuousAt
      (hcontAt false 1 ⟨by norm_num,le_rfl⟩) (𝓝[<] 1)
      (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds) hnear1
  apply transition_flip R L (a+s^2) (a-s^2) sp sm (Y true 0) (Y true 1) hsp hsm
    (hn true 0 ⟨le_rfl,by norm_num⟩) (hn true 1 ⟨by norm_num,le_rfl⟩) hRup
  · simpa only [Y,LegendreFiniteCrossingLifts318.lift_start] using hRlo
  · exact hLup
  · simpa only [Y,LegendreFiniteCrossingLifts318.lift_opposite_end] using hLlo
end LegendreAdjacentTransitionFlip318
