module
public import PELOriginalContactBranchNormalForm318
public section
noncomputable section
namespace PELOriginalContactBranchParameters318
open Set Filter Topology
open scoped OnePoint Manifold ContDiff
open PELUnlevelledComplexBase318 PELOriginalBranchLabels318
open PELOriginalContactBranchSquare318 ComplexSphereCharts318
local instance : ChartedSpace ℂ (UnlevelledBase):=
  unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (UnlevelledBase):=
  unlevelled_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

/-- A constructed original source coordinate with its actual local inverse
and literal original normalized projection. No replacement curve occurs. -/
structure SquareParametrization (p:UnlevelledBase) (B:ℂ→OnePoint ℂ) where
  chart:OpenPartialHomeomorph (UnlevelledBase) ℂ
  center_mem:p∈chart.source
  center_zero:chart p=0
  chart_inverse_holomorphic:∀z∈chart.target,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω chart.symm z
  changeMap:ℂ→ℂ
  inverseChange:ℂ→ℂ
  change_analytic:AnalyticAt ℂ changeMap 0
  change_zero:changeMap 0=0
  change_derivative_ne:deriv changeMap 0≠0
  inverse_analytic:AnalyticAt ℂ inverseChange 0
  inverse_zero:inverseChange 0=0
  left_inverse:(fun w=>inverseChange (changeMap w)) =ᶠ[𝓝 (0:ℂ)] id
  right_inverse:(fun w=>changeMap (inverseChange w)) =ᶠ[𝓝 (0:ℂ)] id
  projection:∀ᶠ w in 𝓝 (0:ℂ),inverseChange w∈chart.target ∧
    normalizedMap (chart.symm (inverseChange w))=B w

@[expose] def fromChart (p:UnlevelledBase)
    (hp:p∈nontrivialStabilizerLocus)
    (c:OpenPartialHomeomorph (OnePoint ℂ) ℂ)
    (hc:c∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint ℂ))
    (hpc:normalizedMap p∈c.source) (B:ℂ→OnePoint ℂ)
    (hB:∀w,c.symm (c (normalizedMap p)+w^2)=B w) : SquareParametrization p B := by
  obtain ⟨e,q,k,hpe,he0,heinv,hq,hq0,hqd,hk,hk0,hl,hr,hproj⟩:=
    PELOriginalContactBranchNormalForm318.normal_form p hp c hc hpc
  refine ⟨e,hpe,he0,heinv,q,k,hq,hq0,hqd,hk,hk0,hl,hr,?_⟩
  filter_upwards [hproj] with w hw
  refine ⟨hw.1,?_⟩
  calc
    normalizedMap (e.symm (k w))=c.symm (c (normalizedMap (e.symm (k w)))):=
      (c.left_inv hw.2.1).symm
    _=c.symm (c (normalizedMap p)+w^2):=congrArg c.symm hw.2.2
    _=B w:=hB w

/-- Literal t=a+w² at an actual point of the full original genus-five
ramification locus, retaining every point above that labeled branch. -/
@[expose] def finite (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus) (a:ℂ)
    (ha:normalizedMap p=(a:OnePoint ℂ)) :
    SquareParametrization p (fun w=>(a+w^2:ℂ)) := by
  apply fromChart p hp affine
    (IsManifold.subset_maximalAtlas (show affine∈atlas ℂ (OnePoint ℂ) from ⟨false,rfl⟩))
    (by rw [ha];exact affine_mem a) (fun w=>(a+w^2:ℂ))
  intro w
  rw [ha,affine_coe,affine_symm]

/-- Literal reciprocal t=w² at EVERY actual source point above original
label210. The eight infinity branches are not collapsed to one point. -/
@[expose] def infinity (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
    (h∞:normalizedMap p=∞) :
    SquareParametrization p (fun w=>SphereInversion318.inversion (w^2:ℂ)) := by
  apply fromChart p hp reciprocal
    (IsManifold.subset_maximalAtlas (show reciprocal∈atlas ℂ (OnePoint ℂ) from ⟨true,rfl⟩))
    (by rw [h∞];exact reciprocal_mem_infty) (fun w=>SphereInversion318.inversion (w^2:ℂ))
  intro w
  rw [h∞,reciprocal_infty,zero_add,reciprocal_symm]
end PELOriginalContactBranchParameters318
