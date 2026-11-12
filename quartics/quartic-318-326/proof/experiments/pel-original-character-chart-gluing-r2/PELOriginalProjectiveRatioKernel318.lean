module
public import PELOriginalTripleDirectionalEvaluation318
public section
noncomputable section
namespace PELOriginalProjectiveRatioKernel318
open Filter Topology
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalAllLevelHolomorphicMap318 ComplexProjectiveComplexAtlas318
variable (τ:ℂ)(hτ:0<τ.im)
/-- The actual independent projective target chart uses a fixed omitted
coordinate model. Its zero Frechet direction implies zero derivatives
of ALL literal ratios, via the genuine inverse linear coordinates. -/
theorem scalar_ratios(x v:ComplexVectors)(j:Label 3)(hj:value τ hτ 3 j x≠0)
    (hk:fderiv ℂ (ratioVector τ hτ 1 j) x v=0):
    ∀r:Label 3,fderiv ℂ (fun z=>value τ hτ 3 r z/value τ hτ 3 j z) x v=0:=by
  let Q:ComplexVectors→({r:Label 3 //r≠j}→ℂ):=
    fun z r=>value τ hτ 3 r.val z/value τ hτ 3 j z
  let e:({r:Label 3 //r≠j}→ℂ)≃L[ℂ]TargetModel 1:=
    (coordinates (Label 3) (0:Label 3) j).toContinuousLinearEquiv
  have hQ:∀z,Q z=e.symm (ratioVector τ hτ 1 j z):=by
    intro z
    exact (e.symm_apply_apply (Q z)).symm
  have hv:HasDerivAt (fun t:ℂ=>ratioVector τ hτ 1 j (x+t • v)) 0 0:=by
    simpa only [zero_smul,add_zero,one_smul,hk] using
      (ratio_differentiable τ hτ 1 j x hj).hasFDerivAt.comp_hasDerivAt 0
        (((hasDerivAt_id (0:ℂ)).smul_const v).const_add x)
  have hq:HasDerivAt (fun t:ℂ=>Q (x+t • v)) 0 0:=by
    have h:=e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hv
    simpa only [←hQ,map_zero] using h
  intro r
  by_cases hr:r=j
  · subst r
    have he:(fun z=>value τ hτ 3 j z/value τ hτ 3 j z)=ᶠ[nhds x] (fun _=>1):=by
      filter_upwards [(PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j).continuous.continuousAt.eventually_ne hj] with z hz
      exact div_self hz
    have hd:(fderiv ℂ (fun z=>value τ hτ 3 j z/value τ hτ 3 j z) x)=0:=by
      rw [he.fderiv_eq]
      exact (hasFDerivAt_const x (1:ℂ)).fderiv
    rw [hd]
    rfl
  · have hp:HasDerivAt (fun t:ℂ=>value τ hτ 3 r (x+t • v)/value τ hτ 3 j (x+t • v)) 0 0:=by
      have h:=(ContinuousLinearMap.proj (R:=ℂ) ⟨r,hr⟩).hasFDerivAt.comp_hasDerivAt 0 hq
      simpa only [Q,ContinuousLinearMap.proj_apply,map_zero] using h
    have hd:DifferentiableAt ℂ (fun z=>value τ hτ 3 r z/value τ hτ 3 j z) x:=
      (PELOriginalLevelPowerSections318.holomorphic τ hτ 3 r x).div
        (PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j x) hj
    have h:=hd.hasFDerivAt.comp_hasDerivAt 0
      (((hasDerivAt_id (0:ℂ)).smul_const v).const_add x)
    have h':HasDerivAt (fun t:ℂ=>value τ hτ 3 r (x+t • v)/value τ hτ 3 j (x+t • v))
        (fderiv ℂ (fun z=>value τ hτ 3 r z/value τ hτ 3 j z) x v) 0:=by
      simpa only [zero_smul,add_zero,one_smul] using h
    exact h'.unique hp
end PELOriginalProjectiveRatioKernel318
