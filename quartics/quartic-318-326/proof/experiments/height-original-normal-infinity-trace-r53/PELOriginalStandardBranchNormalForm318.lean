module
public import PELOriginalNormalizedBranchSquare318
public import AnalyticSquaredBaseChange318
public import RiemannChartDerivative318
public section
noncomputable section
namespace PELOriginalStandardBranchNormalForm318
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

/-- Normalize the ORIGINAL local square into ANY specified genuine sphere
atlas chart, constructing the required source-coordinate correction.
In particular this yields t-a=w² at finite branches and reciprocal t=w²
at infinity, rather than silently retaining an unrelated maximal chart. -/
theorem normal_form (p:CharacterBase i)
    (hp:normalizedMap i p=∞ ∨ normalizedMap i p=(0:ℂ) ∨
      normalizedMap i p=(1:ℂ) ∨ normalizedMap i p=(branchParameter i:ℂ))
    (c:OpenPartialHomeomorph (OnePoint ℂ) ℂ)
    (hc:c∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint ℂ))
    (hpc:normalizedMap i p∈c.source) :
    ∃(e:OpenPartialHomeomorph (CharacterBase i) ℂ) (q k:ℂ→ℂ),
      p∈e.source ∧ e p=0 ∧
      (∀z∈e.target,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm z) ∧
      AnalyticAt ℂ q 0 ∧ q 0=0 ∧ deriv q 0≠0 ∧
      AnalyticAt ℂ k 0 ∧ k 0=0 ∧
      (fun w=>k (q w)) =ᶠ[𝓝 (0:ℂ)] id ∧
      (fun w=>q (k w)) =ᶠ[𝓝 (0:ℂ)] id ∧
      (∀ᶠ w in 𝓝 (0:ℂ),k w∈e.target ∧
        normalizedMap i (e.symm (k w))∈c.source ∧
        c (normalizedMap i (e.symm (k w)))=c (normalizedMap i p)+w^2) := by
  obtain ⟨e,b,hpe,hpb,he0,hb0,hmodel,hehol,heinverse,hbhol,hbinverse⟩:=
    PELOriginalNormalizedBranchSquare318.branch_square i p hp
  have het:0∈e.target:=by simpa only [he0] using e.map_source hpe
  have hbt:0∈b.target:=by simpa only [hb0] using b.map_source hpb
  have hbi:b.symm 0=normalizedMap i p:=by rw [←hb0,b.left_inv hpb]
  let K:OpenPartialHomeomorph ℂ ℂ:=b.symm.trans c
  have hKsource:0∈K.source:=⟨hbt,by simpa only [hbi] using hpc⟩
  have hK0:K 0=c (normalizedMap i p):=by change c (b.symm 0)=_;rw [hbi]
  have hKC:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω K 0:=
    (contMDiffAt_of_mem_maximalAtlas hc (show b.symm 0∈c.source by rw [hbi];exact hpc)).comp 0
      (hbinverse 0 hbt)
  have hKA:AnalyticAt ℂ K 0:=(contMDiffAt_iff_contDiffAt.mp hKC).analyticAt
  have hKne:deriv K 0≠0:=RiemannChartDerivative318.derivative_ne_zero K hKsource hKA
    (ComplexHolomorphicChartInverse318.inverse_analytic K hKsource hKA)
  let f:ℂ→ℂ:=fun z=>K z-K 0
  have hf:AnalyticAt ℂ f 0:=hKA.sub analyticAt_const
  have hf0:f 0=0:=sub_self _
  have hfd:deriv f 0≠0:=by simpa only [f,deriv_sub_const] using hKne
  obtain ⟨q,k,hq,hq0,hqd,hk,hk0,hleft,hright,hsquare⟩:=
    AnalyticSquaredBaseChange318.normalize f hf hf0 hfd
  have hnSource:∀ᶠ z in 𝓝 (0:ℂ),z∈e.target ∧ normalizedMap i (e.symm z)∈c.source:=by
    have hec:ContinuousAt e.symm 0:=e.continuousAt_symm het
    have hcenter:e.symm 0=p:=by rw [←he0,e.left_inv hpe]
    have hn:ContinuousAt (fun z=>normalizedMap i (e.symm z)) 0:=
      (PELOriginalNormalizedDoubleCover318.continuous i).continuousAt.comp hec
    have hh:∀ᶠ z in 𝓝 (0:ℂ),normalizedMap i (e.symm z)∈c.source:=
      hn.eventually (by simpa only [hcenter] using c.open_source.mem_nhds hpc)
    exact (e.open_target.mem_nhds het).and hh
  have hbase:∀ᶠ z in 𝓝 (0:ℂ),z∈e.target ∧ normalizedMap i (e.symm z)∈c.source ∧
      c (normalizedMap i (e.symm z))=K 0+(q z)^2:=by
    filter_upwards [hnSource,hsquare] with z hz hsq
    have hx:e.symm z∈e.source:=e.map_target hz.1
    have hb: b (normalizedMap i (e.symm z))=z^2:=by
      rw [(hmodel _ hx).2,e.right_inv hz.1]
    have hv:b.symm (z^2)=normalizedMap i (e.symm z):=by
      rw [←hb,b.left_inv (hmodel _ hx).1]
    have hh:K (z^2)=c (normalizedMap i (e.symm z)):=congrArg c hv
    refine ⟨hz.1,hz.2,?_⟩
    change q z^2=K (z^2)-K 0 at hsq
    rw [hh] at hsq
    linear_combination -hsq
  have hkt:Tendsto k (𝓝 0) (𝓝 0):=by simpa only [hk0] using hk.continuousAt
  refine ⟨e,q,k,hpe,he0,heinverse,hq,hq0,hqd,hk,hk0,hleft,hright,?_⟩
  filter_upwards [hkt.eventually hbase,hright] with w hw hr
  exact ⟨hw.1,hw.2.1,by simpa only [hr,hK0] using hw.2.2⟩
end PELOriginalStandardBranchNormalForm318
