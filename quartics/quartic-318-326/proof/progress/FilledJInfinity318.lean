module
public import FilledJPole318
public import FilledJHolomorphic318
public import Mathlib.Topology.Compactification.OnePoint.Basic
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318
open PeterssonQuotient318 ActualSingleCusp318 FilledCuspCharts318 FilledJ318 QuotientJ318
open HighQParameter318 ActualCuspHomeomorph318
namespace FilledJInfinity318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def localJ (q:ℂ) : OnePoint ℂ := by
  classical
  exact if q=0 then OnePoint.infty else ↑(ActualQJ318.G q/q)

@[simp] theorem localJ_zero : localJ 0=OnePoint.infty := by simp [localJ]

theorem localJ_continuousAt_zero : ContinuousAt localJ 0 := by
  have hp : Tendsto (fun q:ℂ=>ActualQJ318.G q/q) (𝓝[≠] 0) (coclosedCompact ℂ) := by
    rw [Filter.coclosedCompact_eq_cocompact,←Metric.cobounded_eq_cocompact]
    apply tendsto_cobounded_of_meromorphicOrderAt_neg
    rw [FilledJPole318.local_order]
    exact WithTop.coe_lt_coe.mpr (by norm_num : (-1:ℤ)<0)
  have ht := OnePoint.tendsto_coe_infty.comp hp
  have hlocal:Tendsto localJ (𝓝[≠] 0) (𝓝 (OnePoint.infty:OnePoint ℂ)) := by
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hn:q≠0 := hq
    simp only [Function.comp_apply,localJ,if_neg hn]
  change Tendsto localJ (𝓝 0) (𝓝 (localJ 0))
  rw [localJ_zero,←nhdsNE_sup_pure,tendsto_sup]
  exact ⟨hlocal,by simpa only [localJ_zero] using tendsto_pure_nhds localJ 0⟩

theorem localJ_continuousAt (q:ℂ) (hq:‖q‖<1) : ContinuousAt localJ q := by
  classical
  by_cases hzero:q=0
  · subst q;exact localJ_continuousAt_zero
  · have h := OnePoint.continuous_coe.continuousAt.comp
      ((ActualQJ318.G_differentiableAt q hq).continuousAt.div continuousAt_id hzero)
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hzero] with z hz
    simp only [Function.comp_apply,localJ,if_neg hz,Pi.div_apply,id_eq]

/-- The actual extension to the one-point compactification target; the new
cusp maps to infinity rather than the totalized value used for meromorphic germs. -/
@[expose] def jInfinity (N:ℕ) (z:Filled N) : OnePoint ℂ := by
  classical
  exact if z=cusp N then OnePoint.infty else ↑(filledJ N z)

theorem jInfinity_original (N:ℕ) (b:Base (image N)) :
    jInfinity N (original N b)=↑(jMap N b) := by
  simp only [jInfinity,if_neg (original_ne_cusp N b),filledJ_original]

@[simp] theorem jInfinity_cusp (N:ℕ) : jInfinity N (cusp N)=OnePoint.infty := by
  simp [jInfinity]

theorem jInfinity_disc (N:ℕ) (q:disc) : jInfinity N (cuspChart N q)=localJ q := by
  classical
  have he:cuspChart N q=cusp N ↔ (q:ℂ)=0 := by
    constructor
    · intro h;exact congrArg Subtype.val ((cuspChart_isOpenEmbedding N).injective h)
    · intro h;exact congrArg (cuspChart N) (Subtype.ext h)
  simp only [jInfinity,localJ,he,filledJ_disc]

theorem jInfinity_continuous (N:ℕ) (hN:5≤N) : Continuous (jInfinity N) := by
  let f : Base (image N) ⊕ disc → Filled N := Sum.elim (original N) (cuspChart N)
  have hc:Continuous f := continuous_sum_dom.mpr
    ⟨(original_isOpenEmbedding N).continuous,(cuspChart_isOpenEmbedding N).continuous⟩
  have ho:IsOpenMap f := (original_isOpenEmbedding N).isOpenMap.sumElim
    (cuspChart_isOpenEmbedding N).isOpenMap
  have hs:Function.Surjective f := by
    intro z
    rcases TwoChartGluing318.jointly_surjective (overlap N) z with ⟨b,hb⟩ | ⟨q,hq⟩
    · exact ⟨Sum.inl b,hb⟩
    · exact ⟨Sum.inr q,hq⟩
  have hf:IsOpenQuotientMap f := ⟨hs,hc,ho⟩
  apply hf.isQuotientMap.continuous_iff.mpr
  apply continuous_sum_dom.mpr
  constructor
  · have he:(jInfinity N ∘ f) ∘ Sum.inl = fun b=> (jMap N b : OnePoint ℂ) := by
      funext b;exact jInfinity_original N b
    rw [he]
    exact OnePoint.continuous_coe.comp (HolomorphicQuotientJ318.jMap_continuous N hN)
  · have he:(jInfinity N ∘ f) ∘ Sum.inr = fun q:disc=> localJ q := by
      funext q;exact jInfinity_disc N q
    rw [he]
    apply continuous_iff_continuousAt.mpr
    intro q
    apply (localJ_continuousAt q ?_).comp continuous_subtype_val.continuousAt
    exact lt_trans q.property (by
      change Real.exp (-2*Real.pi*height)<1
      apply Real.exp_lt_one_iff.mpr
      nlinarith [Real.pi_pos,height_positive])

end FilledJInfinity318
