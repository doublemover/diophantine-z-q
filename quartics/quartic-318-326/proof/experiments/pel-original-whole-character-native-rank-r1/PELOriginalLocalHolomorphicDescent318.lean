module
public import PELActualArithmeticCollar318
public import ComplexSphereJoukowski318
public section
noncomputable section
namespace PELOriginalLocalHolomorphicDescent318
open Set Filter Topology
open scoped Manifold ContDiff OnePoint
open QuaternionicJointPeriodTopology318 PELUnlevelledComplexBase318
open PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318
open PELPrincipalBaseHolomorphy318 HolomorphicQuotientCoverCharts318
open HolomorphicQuotientCoverMaps318 PELEffectiveNormOneAction318
open PELRegularTransitionHolomorphy318 PELOriginalChartLift318
open PELOriginalBranchLabels318 PELStabilizerLocusInvariant318
open ComplexSphereCharts318
set_option maxHeartbeats 3200000
local instance : ChartedSpace ℂ HalfPlane:=halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane:=halfPlane_manifold
local instance : ChartedSpace ℂ UnlevelledBase:=unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase:=unlevelled_manifold
local instance : ChartedSpace ℂ MaximalBase:=maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase:=maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

/-- Pointwise descent through the unchanged norm-one covering needs only
an actual holomorphic lift germ at this representative, not a global lift. -/
theorem normOne_local (F:UnlevelledBase→OnePoint ℂ) (a:HalfPlane)
    (ha:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (F ∘ PELUnlevelledComplexBase318.projection) a) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F (PELUnlevelledComplexBase318.projection a) := by
  let q:=PELUnlevelledComplexBase318.projection
  let B:=quotientChart (E:=ℂ) q covering a
  let A:=chartAt ℂ a
  have hp:q a∈B.source:=quotientChart_center q covering a
  have ht:=B.map_source hp
  have hvalue:B (q a)=A a:=quotientChart_center_value q covering a
  have hA:=contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) ht.1
  have hae:A.symm (B (q a))=a := by rw [hvalue];exact A.left_inv (mem_chart_source ℂ a)
  have ha':ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (F ∘ q) (A.symm (B (q a))) := by
    rw [hae];exact ha
  have hlocal:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (F ∘ B.symm) (B (q a)) := by
    apply (ha'.comp _ hA).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun z=>by
      change F (B.symm z)=F (q (A.symm z))
      rw [show B.symm z=q (A.symm z) from quotientChart_symm q covering a z])
  have hB:=contMDiffAt_of_mem_maximalAtlas
    (quotientChart_maximal q covering effective_holomorphic a) hp
  apply (hlocal.comp _ hB).congr_of_eventuallyEq
  filter_upwards [B.open_source.mem_nhds hp] with x hx
  exact congrArg F (B.left_inv hx).symm

/-- The original full-normalizer quotient has genuine local holomorphic
sections at regular points. This proof uses its actual retained charts
and the analytic inverse of their true partial homeomorphism. -/
theorem maximal_regular_local (F:MaximalBase→OnePoint ℂ) (p:UnlevelledBase)
    (hp:p∉nontrivialStabilizerLocus)
    (hF:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (F ∘ PELOriginalMaximalQuotient318.projection) p) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F (PELOriginalMaximalQuotient318.projection p) := by
  let q:=PELOriginalMaximalQuotient318.projection p
  obtain ⟨U,g,hU,hpU,hgs,hgv,_⟩:=PELRegularQuotientChart318.exists_regular_chart p hp
  have hqg:q∈g.source:=by rw [hgs];exact ⟨p,hpU,rfl⟩
  let A:=chartAt ℂ p
  have hpA:p∈A.source:=mem_chart_source ℂ p
  have hv:g q=A p:=hgv p hpU
  have hzA:g q∈A.target:=by rw [hv];exact A.map_source hpA
  have hAI:=contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hzA
  have hF':ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (F ∘ PELOriginalMaximalQuotient318.projection) (A.symm (g q)) := by
    rw [hv,A.left_inv hpA];exact hF
  have hK:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (F ∘ g.symm) (g q) := by
    apply (hF'.comp _ hAI).congr_of_eventuallyEq
    filter_upwards [inverse_regular_formula p U hU hpU g hgs hgv] with w hw
    exact congrArg F hw
  let B:=chosenChart q
  have hqB:q∈B.source:=chosenChart_center q
  let H:=g.symm.trans B
  have hxH:g q∈H.source:=⟨g.map_source hqg,by simpa only [g.left_inv hqg] using hqB⟩
  have hH:AnalyticAt ℂ H (g q):=
    in_regular_coordinate p U hU hpU g hgs hgv B (chosenChart_original q) hqB
  have hInv:=ComplexHolomorphicChartInverse318.inverse_analytic H hxH hH
  have hInv':AnalyticAt ℂ (fun w=>g (B.symm w)) (B q) := by
    simpa only [H,OpenPartialHomeomorph.coe_trans,Function.comp_apply,g.left_inv hqg,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,OpenPartialHomeomorph.symm_symm] using hInv
  have hK':ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (F ∘ g.symm) (g (B.symm (B q))) := by
    rw [B.left_inv hqB];exact hK
  have hlocal:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (F ∘ B.symm) (B q) := by
    apply (hK'.comp _ (contMDiffAt_iff_contDiffAt.mpr hInv'.contDiffAt)).congr_of_eventuallyEq
    have ht:Tendsto B.symm (𝓝 (B q)) (𝓝 q) := by
      simpa only [B.left_inv hqB] using (B.continuousAt_symm (B.map_source hqB)).tendsto
    filter_upwards [ht.eventually (g.open_source.mem_nhds hqg)] with w hw
    exact congrArg F (g.left_inv hw).symm
  have hB:=contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (show B∈atlas ℂ MaximalBase from ⟨q,rfl⟩)) hqB
  apply (hlocal.comp _ hB).congr_of_eventuallyEq
  filter_upwards [B.open_source.mem_nhds hqB] with y hy
  exact congrArg F (B.left_inv hy).symm

/-- Pointwise two-stage descent in the same original complex structures.
Only the actual finite branch image is excluded, not an assumed covering. -/
theorem upper_regular_local (F:MaximalBase→OnePoint ℂ) (τ:HalfPlane)
    (hq:PELMaximalHalfOctagonOriginalPoints318.maximalProjection τ∉branchImage)
    (hF:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (F ∘ PELMaximalHalfOctagonOriginalPoints318.maximalProjection) τ) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F
      (PELMaximalHalfOctagonOriginalPoints318.maximalProjection τ) := by
  have hp:PELUnlevelledComplexBase318.projection τ∉nontrivialStabilizerLocus :=
    fun h=>hq ((branch_image_iff _).mpr h)
  exact maximal_regular_local F _ hp
    (normOne_local (F ∘ PELOriginalMaximalQuotient318.projection) τ hF)
end PELOriginalLocalHolomorphicDescent318
