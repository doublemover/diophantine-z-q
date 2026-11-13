module
public import PELOriginalContactFiniteMapGerm318
public section
noncomputable section
namespace PELOriginalContactInfinityMapGerm318
open Set Filter
open scoped Topology OnePoint
open PELUnlevelledComplexBase318 PELOriginalContactRootFunctions318
open PELOriginalContactBranchSquare318 PELOriginalCommonContactBase318
open PELOriginalBranchLabels318 PELOriginalContactRootExtensions318
open PELOriginalContactParameterLocality318 PELOriginalCompletedContactPoints318
open FourRootNormalizedPointCharts318
local instance : TopologicalSpace (Completed branches):=FourRootGluedTopology318.topology branches
variable (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus) (h:normalizedMap p=∞)

@[expose] def u:ℂ→ℂ:=FourRootInfinityExtension318.parameter (infinityUnits p hp h)
@[expose] def ratios (k:Fin 4):ℂ→ℂ:=FourRootInfinityExtension318.ratio (infinityUnits p hp h) k
lemma u_zero:u p hp h 0=0:=by
  obtain ⟨inv,hA,hS,hG,hU,h0,hrest⟩:=(PELOriginalContactRootExtensions318.infinity p hp h).choose_spec
  exact h0
lemma u_analytic:AnalyticAt ℂ (u p hp h) 0:=by
  obtain ⟨inv,hA,hS,hG,hU,hrest⟩:=(PELOriginalContactRootExtensions318.infinity p hp h).choose_spec
  exact hU
lemma ratios_analytic (k:Fin 4):AnalyticAt ℂ (ratios p hp h k) 0:=by
  obtain ⟨inv,hA,hS,hG,hU,h0,hD,hI,hI0,hL,hR,hRat,hrest⟩:=
    (PELOriginalContactRootExtensions318.infinity p hp h).choose_spec
  exact (hRat k).1
lemma ratios_center (k:Fin 4):ratios p hp h k 0=(infinityCenter p hp h).val k:=rfl
lemma equations:∀ᶠw in 𝓝 (0:ℂ),ratios p hp h 0 w=1 ∧
    ∀k,ratios p hp h k w^2=1+(branches 0-branches k)*(u p hp h w)^2:=by
  obtain ⟨inv,hA,hS,hG,hU,h0,hD,hI,hI0,hL,hR,hRat,hE,hrest⟩:=
    (PELOriginalContactRootExtensions318.infinity p hp h).choose_spec
  exact hE
lemma punctured_values:∀ᶠw in 𝓝[≠] (0:ℂ),
    u p hp h w=(roots (source (infinityParameter p hp h) w) 0)⁻¹ ∧
    ∀k,ratios p hp h k w=roots (source (infinityParameter p hp h) w) k/
      roots (source (infinityParameter p hp h) w) 0:=by
  obtain ⟨inv,hA,hS,hG,hU,h0,hD,hI,hI0,hL,hR,hRat,hE,hF⟩:=
    (PELOriginalContactRootExtensions318.infinity p hp h).choose_spec
  exact hF

@[expose] def center:InfinityPoints branches:=
  ⟨(0,(infinityCenter p hp h).val),(infinityCenter p hp h).property.1,by
    intro k
    simpa only [zero_pow (by decide:2≠0),mul_zero,add_zero] using
      (infinityCenter p hp h).property.2 k⟩
@[expose] def germ (w:ℂ):InfinityPoints branches:=
  if hw:ratios p hp h 0 w=1 ∧
      ∀k,ratios p hp h k w^2=1+(branches 0-branches k)*(u p hp h w)^2 then
    ⟨(u p hp h w,fun k=>ratios p hp h k w),hw⟩
  else center p hp h
lemma value:(fun w=>(germ p hp h w).val)=ᶠ[𝓝 (0:ℂ)]
    (fun w=>(u p hp h w,fun k=>ratios p hp h k w)):=by
  filter_upwards [equations p hp h] with w hw
  simp only [germ,dif_pos hw]
lemma germ_zero:germ p hp h 0=center p hp h:=by
  have hz:ratios p hp h 0 0=1 ∧
      ∀k,ratios p hp h k 0^2=1+(branches 0-branches k)*(u p hp h 0)^2:=by
    constructor
    · exact (infinityCenter p hp h).property.1
    · intro k
      rw [u_zero,zero_pow (by decide:2≠0),mul_zero,add_zero]
      exact (infinityCenter p hp h).property.2 k
  apply Subtype.ext
  simp only [germ,dif_pos hz,u_zero]
  rfl
lemma continuous:ContinuousAt (germ p hp h) 0:=by
  have hs:ContinuousAt (fun w:ℂ k=>ratios p hp h k w) 0:=
    continuousAt_pi.mpr (fun k=>(ratios_analytic p hp h k).continuousAt)
  have hv:ContinuousAt (fun w=>(germ p hp h w).val) 0:=
    ((u_analytic p hp h).continuousAt.prodMk hs).congr_of_eventuallyEq (value p hp h)
  exact hv.subtype_mk _

lemma regular_first_root_ne (x:UnlevelledBase) (hx:x∈RegularSource):roots x 0≠0:=by
  intro hz
  have hs:=roots_square x hx 0
  rw [hz,zero_pow (by decide:2≠0)] at hs
  have hb:base x=branches 0:=sub_eq_zero.mp hs.symm
  exact ((FourRootPuncturedRegularity318.denominator_ne_iff branches (base x)).mp
    (denominator_ne x hx) 0) hb

/-- Exact infinity-chart formula for the FIXED completed map on a whole
neighborhood. The center is its actual sign triple; the punctured overlap
is the original coordinate transformation1/z0,zk/z0. -/
theorem map_germ:(fun w=>completedMap (source (infinityParameter p hp h) w))=ᶠ[𝓝 (0:ℂ)]
    (fun w=>infinityChart branches (germ p hp h w)):=by
  have hf:=eventually_nhdsWithin_iff.mp (punctured_values p hp h)
  have hr:=eventually_nhdsWithin_iff.mp
    (PELOriginalContactRootBranchSource318.infinity_regular (infinityParameter p hp h))
  filter_upwards [hf,hr,value p hp h] with w hfw hrw hv
  by_cases hw:w=0
  · subst w
    rw [source_zero,completedMap_infinity p hp h,germ_zero]
    exact (infinityChart_zero branches (infinityCenter p hp h)).symm
  · have hs:=hrw hw
    have hz:=regular_first_root_ne _ hs.1
    have hfw:=hfw hw
    have hu:(germ p hp h w).val.1≠0:=by
      rw [hv]
      exact hfw.1.symm ▸ inv_ne_zero hz
    rw [completedMap_regular _ hs.1,infinityChart_nonzero branches _ hu]
    apply congrArg Sum.inl
    apply Subtype.ext
    apply Prod.ext
    · change base (source (infinityParameter p hp h) w)=
        branches 0+((germ p hp h w).val.1^2)⁻¹
      rw [hv,hfw.1,inv_pow,inv_inv,roots_square _ hs.1 0]
      ring
    · funext k
      change roots (source (infinityParameter p hp h) w) k=
        (germ p hp h w).val.2 k/(germ p hp h w).val.1
      rw [hv,hfw.2 k,hfw.1]
      field_simp [hz]

theorem along_source_continuous:
    ContinuousAt (fun w=>completedMap (source (infinityParameter p hp h) w)) 0:=
  ((FourRootGluedTopology318.infinityChart_continuous branches).continuousAt.comp
    (continuous p hp h)).congr_of_eventuallyEq (map_germ p hp h)
end PELOriginalContactInfinityMapGerm318
