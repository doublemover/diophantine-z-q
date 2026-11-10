module
public import PELOriginalCharacterRegularTransition318
public section
noncomputable section
namespace PELOriginalCharacterTransition318
open PELUnlevelledComplexBase318 PELOriginalCharacterQuotient318 PELOriginalCharacterTopologicalAtlas318
open PELOriginalCharacterChartLift318
open PELOriginalCharacterRegularTransition318 Filter Topology
set_option maxHeartbeats 1700000
variable (i : Fin 4)

/-- Every transition between retained original quotient charts is
holomorphic, INCLUDING a branch point. Continuity comes from the same
partial homeomorphisms; punctured holomorphy uses the actual finite
exceptional image, so no replacement quotient complex structure is assumed. -/
theorem original_transition (e f : OpenPartialHomeomorph (CharacterBase i) ℂ)
    (he : OriginalChart i e) (hf : OriginalChart i f) (q : (CharacterBase i))
    (hqe : q∈e.source) (hqf : q∈f.source) :
    AnalyticAt ℂ (fun z => e (f.symm z)) (f q) := by
  by_cases hq : q∈exceptionalImage i
  · obtain ⟨W,hW,hqW,hiso⟩ := exceptional_neighborhood i q hq
    have ht : Tendsto f.symm (𝓝 (f q)) (𝓝 q) := by
      simpa only [f.left_inv hqf] using (f.continuousAt_symm (f.map_source hqf)).tendsto
    have hcont : ContinuousAt (fun z => e (f.symm z)) (f q) := by
      have he' : ContinuousAt e (f.symm (f q)) := by
        simpa only [f.left_inv hqf] using e.continuousAt hqe
      exact he'.comp (f.continuousAt_symm (f.map_source hqf))
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hcont
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (ht.eventually (hW.mem_nhds hqW)),
      eventually_nhdsWithin_of_eventually_nhds
        (ht.eventually (e.open_source.mem_nhds hqe)),
      eventually_nhdsWithin_of_eventually_nhds
        (f.open_target.mem_nhds (f.map_source hqf)),self_mem_nhdsWithin] with z hzW hze hzf hzne
    have hreg : f.symm z∉exceptionalImage i := by
      intro hb
      have hEq := (hiso (f.symm z) hzW).mp hb
      apply hzne
      calc z=f (f.symm z) := (f.right_inv hzf).symm
           _=f q := congrArg f hEq
    have ha := regular_transition i e f he hf (f.symm z) hze (f.map_target hzf) hreg
    rw [f.right_inv hzf] at ha
    exact ha.differentiableAt
  · exact regular_transition i e f he hf q hqe hqf hq

/-- The whole actual transition source, not merely a dense open subset,
is covered by the analytic argument. -/
theorem transition_analyticOn (e f : OpenPartialHomeomorph (CharacterBase i) ℂ)
    (he : OriginalChart i e) (hf : OriginalChart i f) :
    AnalyticOnNhd ℂ (e.symm.trans f) (e.symm.trans f).source := by
  intro z hz
  have ha := original_transition i f e hf he (e.symm z) hz.2 (e.map_target hz.1)
  rw [e.right_inv hz.1] at ha
  exact ha
end PELOriginalCharacterTransition318
