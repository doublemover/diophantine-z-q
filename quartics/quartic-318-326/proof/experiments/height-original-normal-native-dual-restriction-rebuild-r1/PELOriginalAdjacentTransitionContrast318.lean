module
public import PELOriginalBranchCrossingArcs318
public section
noncomputable section
namespace PELOriginalAdjacentTransitionContrast318
open Set Filter
open scoped Topology OnePoint
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 PELOriginalGlobalHalfPlaneSheets318
open PELOriginalRealStripCover318 PELOriginalStripEndpointMatching318
open PELOriginalBranchCrossingArcs318 SimpleBranchCrossingPaths318
variable {i:Fin 4}

/-- Small positive square offsets approach the branch from the actual
left/right real sides. This produces the neighborhood used to keep the
crossing endpoints in their original adjacent intervals. -/
lemma small_offsets (a:ℝ) (L R:Interval i)
    (hL:∀ᶠ x in 𝓝[<] a,x∈L.carrier) (hR:∀ᶠ x in 𝓝[>] a,x∈R.carrier) :
    ∀ᶠ s in 𝓝 (0:ℝ),0<s → a-s^2∈L.carrier ∧ a+s^2∈R.carrier := by
  have hm:Tendsto (fun s:ℝ=>a-s^2) (𝓝[>] 0) (𝓝[<] a):=by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh:ContinuousAt (fun s:ℝ=>a-s^2) 0:=by fun_prop
      simpa only [zero_pow (by decide : 2≠0),sub_zero] using hh.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change a-s^2<a
      have hh:0<s^2:=sq_pos_of_pos hs
      linarith
  have hp:Tendsto (fun s:ℝ=>a+s^2) (𝓝[>] 0) (𝓝[>] a):=by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh:ContinuousAt (fun s:ℝ=>a+s^2) 0:=by fun_prop
      simpa only [zero_pow (by decide : 2≠0),add_zero] using hh.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change a<a+s^2
      have hh:0<s^2:=sq_pos_of_pos hs
      linarith
  exact eventually_nhdsWithin_iff.mp ((hm.eventually hL).and (hp.eventually hR))

/-- The ACTUAL original transitions on intervals adjacent to a simple
branch are different. Construct the original square lifts, identify each
with one fixed global halfplane sheet, and take the genuine real endpoint
limits through the already constructed whole-strip sheets. Common right
endpoint forces one match; distinct left endpoints force the other.
No monodromy, sign-switch, or boundary-identification input is assumed. -/
theorem adjacent_contrast (p:CharacterBase i) (a:ℝ)
    (ha:normalizedMap i p=(a:ℂ))
    (hb:(a:ℂ)=0 ∨ (a:ℂ)=1 ∨ (a:ℂ)=branchParameter i)
    (L R:Interval i)
    (hL:∀ᶠ x in 𝓝[<] a,x∈L.carrier) (hR:∀ᶠ x in 𝓝[>] a,x∈R.carrier) :
    ∃e:BaseFiber i true,L.transition e≠R.transition e := by
  let V:Set ℂ:={z|0<z.re → a-z.re^2∈L.carrier ∧ a+z.re^2∈R.carrier}
  have hV:V∈𝓝 (0:ℂ):=by
    have hh:=(Complex.continuous_re.continuousAt : ContinuousAt Complex.re (0:ℂ)).eventually
      (small_offsets a L R hL hR)
    exact hh
  obtain ⟨s,hs,F,hsmall,hcont,hproj,hstart,hend,hsheets⟩:=exists_crossing i p a ha hb V hV
  have hends:a-s^2∈L.carrier ∧ a+s^2∈R.carrier:=by
    have hh:=hsmall true 0 ⟨le_rfl,by norm_num⟩
    rw [rootArc_start] at hh
    exact hh hs
  obtain ⟨e,he⟩:=hsheets true
  obtain ⟨f,hf⟩:=hsheets false
  have hnear0:∀ᶠ t in 𝓝[>] (0:ℝ),t∈Ioo 0 1:=by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht'
    exact ⟨ht,ht'⟩
  have hnear1:∀ᶠ t in 𝓝[<] (1:ℝ),t∈Ioo 0 1:=by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht'
    exact ⟨ht',ht⟩
  have hRup:F true 0=seamValue R true e (a+s^2) hends.2:=
    endpoint R true (baseArc a true s) (F true) e
      (fun t ht=>interior_halfplane a true s t hs ht) he 0 (a+s^2) hends.2
      (baseArc_start a true s) (baseArc_continuous a true s).continuousAt
      (hcont true 0 ⟨le_rfl,by norm_num⟩) (𝓝[>] 0)
      (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds) hnear0
  have hRlo:F false 0=seamValue R false f (a+s^2) hends.2:=
    endpoint R false (baseArc a false s) (F false) f
      (fun t ht=>interior_halfplane a false s t hs ht) hf 0 (a+s^2) hends.2
      (baseArc_start a false s) (baseArc_continuous a false s).continuousAt
      (hcont false 0 ⟨le_rfl,by norm_num⟩) (𝓝[>] 0)
      (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds) hnear0
  have hLup:F true 1=seamValue L true e (a-s^2) hends.1:=
    endpoint L true (baseArc a true s) (F true) e
      (fun t ht=>interior_halfplane a true s t hs ht) he 1 (a-s^2) hends.1
      (baseArc_end a true s) (baseArc_continuous a true s).continuousAt
      (hcont true 1 ⟨by norm_num,le_rfl⟩) (𝓝[<] 1)
      (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds) hnear1
  have hLlo:F false 1=seamValue L false f (a-s^2) hends.1:=
    endpoint L false (baseArc a false s) (F false) f
      (fun t ht=>interior_halfplane a false s t hs ht) hf 1 (a-s^2) hends.1
      (baseArc_end a false s) (baseArc_continuous a false s).continuousAt
      (hcont false 1 ⟨by norm_num,le_rfl⟩) (𝓝[<] 1)
      (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds) hnear1
  have hright:R.transition e=f:=(seam_eq_iff R e f _ hends.2).mp
    (hRup.symm.trans (hstart.trans hRlo))
  refine ⟨e,?_⟩
  intro heq
  have hleft:L.transition e=f:=heq.trans hright
  exact hend (hLup.trans (((seam_eq_iff L e f _ hends.1).mpr hleft).trans hLlo.symm))
end PELOriginalAdjacentTransitionContrast318
