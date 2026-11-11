module
public import ComplexProjectiveRatioCharts318
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public section
noncomputable section
namespace ComplexProjectiveComplexAtlas318
open scoped Manifold ContDiff
open Set Topology ComplexProjectiveQuotientTopology318 ComplexProjectiveRatioCharts318
variable (ι:Type*) [Fintype ι] (j₀:ι)
local instance :DecidableEq ι:=Classical.decEq ι
local instance projectiveTopology:TopologicalSpace (Space ι):=topology ι
abbrev Model:=Affine ι j₀

/-- Permuting the omitted coordinate gives the SAME fixed affine model
for every chart. This is only a coordinate permutation, not transport of
the projective topology or complex structure from another space. -/
@[expose] def omittedEquiv (j:ι):{i:ι //i≠j}≃{i:ι //i≠j₀} where
  toFun i:=⟨Equiv.swap j j₀ i.val,by
    intro h
    apply i.property
    apply (Equiv.swap j j₀).injective
    simpa only [Equiv.swap_apply_left] using h⟩
  invFun i:=⟨Equiv.swap j j₀ i.val,by
    intro h
    apply i.property
    apply (Equiv.swap j j₀).injective
    simpa only [Equiv.swap_apply_right] using h⟩
  left_inv i:=Subtype.ext (by simp)
  right_inv i:=Subtype.ext (by simp)
@[expose] def coordinates (j:ι):Affine ι j ≃ₗ[ℂ] Model ι j₀ where
  toFun w:=fun i=>w ((omittedEquiv ι j₀ j).symm i)
  invFun w:=fun i=>w (omittedEquiv ι j₀ j i)
  left_inv w:=by funext i;simp
  right_inv w:=by funext i;simp
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
@[expose] def localChart (j:ι):OpenPartialHomeomorph (Space ι) (Model ι j₀) where
  toFun p:=coordinates ι j₀ j (toAffine ι j p)
  invFun z:=fromAffine ι j ((coordinates ι j₀ j).symm z)
  source:=domain ι j
  target:=Set.univ
  map_source':=fun _ _=>Set.mem_univ _
  map_target':=fun z _=>fromAffine_mem ι j _
  left_inv':=by
    intro p hp
    rw [LinearEquiv.symm_apply_apply]
    exact from_to ι j p hp
  right_inv':=by
    intro z hz
    rw [to_from,LinearEquiv.apply_symm_apply]
  open_source:=domain_open ι j
  open_target:=isOpen_univ
  continuousOn_toFun:=
    (coordinates ι j₀ j).toContinuousLinearEquiv.continuous.comp_continuousOn
      (toAffine_continuousOn ι j)
  continuousOn_invFun:=
    ((fromAffine_continuous ι j).comp (coordinates ι j₀ j).symm.toContinuousLinearEquiv.continuous).continuousOn
lemma embed_analytic (j:ι)(w:Affine ι j):AnalyticAt ℂ (embed ι j) w:=by
  apply AnalyticAt.pi
  intro i
  by_cases hi:i=j
  · simpa only [embed,dif_pos hi] using (analyticAt_const:AnalyticAt ℂ (fun _:Affine ι j=>(1:ℂ)) w)
  · simpa only [embed,dif_neg hi] using
      ((ContinuousLinearMap.proj (R:=ℂ) ⟨i,hi⟩).analyticAt w)

/-- Every genuine affine transition is a ratio of the actual homogeneous
coordinates, with its denominator nonzero on the WHOLE overlap. -/
lemma analytic_transition (j k:ι):
    AnalyticOnNhd ℂ ((localChart ι j₀ j).symm.trans (localChart ι j₀ k))
      ((localChart ι j₀ j).symm.trans (localChart ι j₀ k)).source:=by
  intro z hz
  let w:Affine ι j:=(coordinates ι j₀ j).symm z
  have hd:embed ι j w k≠0:=
    (mk_mem_domain ι k _ _).mp hz.2
  have ha:AnalyticAt ℂ (fun v:Model ι j₀=>embed ι j ((coordinates ι j₀ j).symm v)) z:=
    (embed_analytic ι j w).comp
      ((coordinates ι j₀ j).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt z)
  have hden:AnalyticAt ℂ (fun v:Model ι j₀=>embed ι j ((coordinates ι j₀ j).symm v) k) z:=
    ((ContinuousLinearMap.proj (R:=ℂ) k).analyticAt _).comp ha
  have hrat:AnalyticAt ℂ (fun v:Model ι j₀=>fun i:{i:ι //i≠k}=>
      embed ι j ((coordinates ι j₀ j).symm v) i.val/
        embed ι j ((coordinates ι j₀ j).symm v) k) z:=by
    apply AnalyticAt.pi
    intro i
    exact (((ContinuousLinearMap.proj (R:=ℂ) i.val).analyticAt _).comp ha).div hden hd
  exact ((coordinates ι j₀ k).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp hrat

@[expose,instance_reducible] def chartedSpace:ChartedSpace (Model ι j₀) (Space ι) where
  atlas:=Set.range (localChart ι j₀)
  chartAt p:=localChart ι j₀ (domain_cover ι p).choose
  mem_chart_source p:=(domain_cover ι p).choose_spec
  chart_mem_atlas p:=⟨_,rfl⟩

/-- The canonical complex atlas on the ACTUAL quotient projective space,
built from its independent affine-ratio charts. -/
theorem complex_manifold:letI:=chartedSpace ι j₀;
    IsManifold 𝓘(ℂ,Model ι j₀) ω (Space ι):=by
  letI:=chartedSpace ι j₀
  apply isManifold_of_contDiffOn
  rintro e e' ⟨j,rfl⟩ ⟨k,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition ι j₀ j k).contDiffOn
      ((localChart ι j₀ j).symm.trans (localChart ι j₀ k)).open_source.uniqueDiffOn
end ComplexProjectiveComplexAtlas318
