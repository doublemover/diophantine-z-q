module
public import PELOriginalStandardBranchNormalForm318
public section
noncomputable section
namespace PELOriginalLiteralBranchParameters318
open Set Filter Topology
open scoped OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 ComplexSphereCharts318
variable (i:Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

/-- A constructed original source coordinate with its actual local inverse
and literal original normalized projection. No replacement curve occurs. -/
structure SquareParametrization (p:CharacterBase i) (B:ℂ→OnePoint ℂ) where
  chart:OpenPartialHomeomorph (CharacterBase i) ℂ
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
    normalizedMap i (chart.symm (inverseChange w))=B w

@[expose] def fromChart (p:CharacterBase i)
    (hp:normalizedMap i p=∞ ∨ normalizedMap i p=(0:ℂ) ∨
      normalizedMap i p=(1:ℂ) ∨ normalizedMap i p=(branchParameter i:ℂ))
    (c:OpenPartialHomeomorph (OnePoint ℂ) ℂ)
    (hc:c∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint ℂ))
    (hpc:normalizedMap i p∈c.source) (B:ℂ→OnePoint ℂ)
    (hB:∀w,c.symm (c (normalizedMap i p)+w^2)=B w) : SquareParametrization i p B := by
  obtain ⟨e,q,k,hpe,he0,heinv,hq,hq0,hqd,hk,hk0,hl,hr,hproj⟩:=
    PELOriginalStandardBranchNormalForm318.normal_form i p hp c hc hpc
  refine ⟨e,hpe,he0,heinv,q,k,hq,hq0,hqd,hk,hk0,hl,hr,?_⟩
  filter_upwards [hproj] with w hw
  refine ⟨hw.1,?_⟩
  calc
    normalizedMap i (e.symm (k w))=c.symm (c (normalizedMap i (e.symm (k w)))):=
      (c.left_inv hw.2.1).symm
    _=c.symm (c (normalizedMap i p)+w^2):=congrArg c.symm hw.2.2
    _=B w:=hB w

/-- Exact finite-branch model t=a+w² on the SAME original character curve. -/
@[expose] def finite (p:CharacterBase i) (a:ℂ)
    (ha:normalizedMap i p=(a:OnePoint ℂ))
    (hb:a=0 ∨ a=1 ∨ a=branchParameter i) :
    SquareParametrization i p (fun w=>(a+w^2:ℂ)) := by
  have hp:normalizedMap i p=∞ ∨ normalizedMap i p=(0:ℂ) ∨
      normalizedMap i p=(1:ℂ) ∨ normalizedMap i p=(branchParameter i:ℂ):=by
    rcases hb with rfl|rfl|rfl
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ha))
  apply fromChart i p hp affine
    (IsManifold.subset_maximalAtlas (show affine∈atlas ℂ (OnePoint ℂ) from ⟨false,rfl⟩))
    (by rw [ha];exact affine_mem a) (fun w=>(a+w^2:ℂ))
  intro w
  rw [ha,affine_coe,affine_symm]

/-- Exact infinity model reciprocal t=w², including its origin, on the
SAME original character curve. The standard sphere inversion is explicit. -/
@[expose] def infinity (p:CharacterBase i) (hp:normalizedMap i p=∞) :
    SquareParametrization i p (fun w=>SphereInversion318.inversion (w^2:ℂ)) := by
  apply fromChart i p (Or.inl hp) reciprocal
    (IsManifold.subset_maximalAtlas (show reciprocal∈atlas ℂ (OnePoint ℂ) from ⟨true,rfl⟩))
    (by rw [hp];exact reciprocal_mem_infty) (fun w=>SphereInversion318.inversion (w^2:ℂ))
  intro w
  rw [hp,reciprocal_infty,zero_add,reciprocal_symm]
end PELOriginalLiteralBranchParameters318
