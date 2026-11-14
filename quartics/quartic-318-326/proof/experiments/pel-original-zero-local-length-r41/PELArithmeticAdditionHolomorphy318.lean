module
public import PELArithmeticRelativeSum318
public import HolomorphicQuotientInverse318
public section
noncomputable section
namespace PELArithmeticAdditionHolomorphy318
open QuaternionicJointPeriodTopology318 PELJointPeriodFamily318 PELJointPeriodDeck318 PELJointComplexAtlas318
open PELPrincipalThreeFreeAction318 PELPrincipalProperAction318 PELPrincipalThreeCovering318
open PELArithmeticComplexFamily318 PELJointRelativeAddition318 PELArithmeticRelativeSum318
open HolomorphicQuotientCoverCharts318 HolomorphicQuotientCoverMaps318 HolomorphicQuotientInverse318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 2000000
local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold
local instance : ChartedSpace Ambient ArithmeticTotal := arithmeticTotalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω ArithmeticTotal := arithmeticTotal_manifold

/-- Addition on the literal arithmetic relative fiber product is jointly
holomorphic in the full test-map sense. Local covering lifts are aligned
by actual base-cover injectivity; base equality is not assumed for arbitrary lifts. -/
theorem arithmeticAdd_holomorphic {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℂ,E) ω N]
    (f g : N → ArithmeticTotal) (hf : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,Ambient) ω f)
    (hg : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,Ambient) ω g)
    (hbase : ∀ y,arithmeticProjection (f y)=arithmeticProjection (g y)) :
    ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,Ambient) ω
      (fun y => arithmeticAdd ⟨(f y,g y),hbase y⟩) := by
  intro x
  obtain ⟨r,a,b,ha,hb,hab,hr⟩ := sum_exists (f x) (g x) (hbase x)
  let A := HolomorphicQuotientCoverCharts318.inverseChart totalQuotient total_covering a
  let B := HolomorphicQuotientCoverCharts318.inverseChart totalQuotient total_covering b
  let F : N → Total := fun y => A (f y)
  let G : N → Total := fun y => B (g y)
  have hfa : f x∈(quotientChart (E:=Ambient) totalQuotient total_covering a).source :=
    ha ▸ quotientChart_center totalQuotient total_covering a
  have hgb : g x∈(quotientChart (E:=Ambient) totalQuotient total_covering b).source :=
    hb ▸ quotientChart_center totalQuotient total_covering b
  have hF : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,Ambient) ω F x :=
    (inverse_holomorphicAt totalQuotient total_covering principal_total_holomorphic a (f x) hfa).comp x (hf x)
  have hG : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,Ambient) ω G x :=
    (inverse_holomorphicAt totalQuotient total_covering principal_total_holomorphic b (g x) hgb).comp x (hg x)
  have hFx : F x=a := by
    change A (f x)=a
    rw [←ha]
    exact total_localHomeomorph.localInverseAt_apply_self
  have hGx : G x=b := by
    change B (g x)=b
    rw [←hb]
    exact total_localHomeomorph.localInverseAt_apply_self
  have heF : ∀ᶠ y in 𝓝 x,totalQuotient (F y)=f y := by
    filter_upwards [(hf x).continuousAt.eventually (A.open_source.mem_nhds hfa.1)] with y hy
    exact HolomorphicQuotientInverse318.inverse_projection totalQuotient total_covering a (f y) hy
  have heG : ∀ᶠ y in 𝓝 x,totalQuotient (G y)=g y := by
    filter_upwards [(hg x).continuousAt.eventually (B.open_source.mem_nhds hgb.1)] with y hy
    exact HolomorphicQuotientInverse318.inverse_projection totalQuotient total_covering b (g y) hy
  let C := base_localHomeomorph.localInverseAt a.1
  have hFa : (F x).1∈C.target := by
    rw [hFx]
    exact base_localHomeomorph.self_mem_localInverseAt_target
  have hGa : (G x).1∈C.target := by
    rw [hGx,←hab]
    exact base_localHomeomorph.self_mem_localInverseAt_target
  have hsame : ∀ᶠ y in 𝓝 x,(F y).1=(G y).1 := by
    filter_upwards [heF,heG,
      (continuous_fst.continuousAt.comp x hF.continuousAt).eventually (C.open_target.mem_nhds hFa),
      (continuous_fst.continuousAt.comp x hG.continuousAt).eventually (C.open_target.mem_nhds hGa)]
      with y hyf hyg hyF hyG
    have hq : baseQuotient (F y).1=baseQuotient (G y).1 := by
      calc
        _ = arithmeticProjection (f y) := congrArg arithmeticProjection hyf
        _ = arithmeticProjection (g y) := hbase y
        _ = baseQuotient (G y).1 := (congrArg arithmeticProjection hyg).symm
    have hleft := C.right_inv hyF
    have hright := C.right_inv hyG
    rw [base_localHomeomorph.localInverseAt_symm] at hleft hright
    exact hleft.symm.trans ((congrArg C hq).trans hright)
  have hadd := relativeAdd_holomorphicAt F G x hF hG hsame
  apply ((totalQuotient_holomorphic _).comp x hadd).congr_of_eventuallyEq
  filter_upwards [heF,heG,hsame] with y hyf hyg hybase
  exact sum_unique (arithmeticAdd_relation ⟨(f y,g y),hbase y⟩)
    ⟨F y,G y,hyf,hyg,hybase,rfl⟩
end PELArithmeticAdditionHolomorphy318
