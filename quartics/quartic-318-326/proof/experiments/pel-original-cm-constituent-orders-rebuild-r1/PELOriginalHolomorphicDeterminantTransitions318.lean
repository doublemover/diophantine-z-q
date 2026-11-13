module
public import PELOriginalAnalyticDeterminantCocycle318
public import PELOriginalCoarseDeterminantMetric318
public section
noncomputable section
namespace PELOriginalHolomorphicDeterminantTransitions318
open QuaternionicJointPeriodTopology318 PELJointComplexAtlas318
open PELUnlevelledComplexBase318 PELOriginalDeterminantCover318
open PELOriginalCoarseDeterminantBundle318 PELOriginalContinuousDeterminantCocycle318
open PELOriginalAnalyticDeterminantCocycle318 Filter
open scoped Topology

/-- Holomorphy of the GENUINE bundle transitions in the actual original
covering coordinates. Both local lifts and the deck label are produced;
no analytic scalar or arbitrary chart compatibility is assumed. -/
theorem transition_analytic (a b τ : HalfPlane)
    (ha : τ∈(chart a).target) (hb : projection τ∈baseSet b) :
    AnalyticAt ℂ (fun z=>transition a b (projection (baseChart.symm z))) (τ:ℂ) := by
  have hat : (τ:ℂ)∈baseChart.target := τ.property
  have heτ : baseChart.symm (τ:ℂ)=τ := baseChart.left_inv (Set.mem_univ τ)
  have hqa : projection τ∈baseSet a := by
    have h := (chart a).map_target ha
    simpa only [chart,IsLocalHomeomorph.localInverseAt_symm] using h
  have hc : ContinuousAt (fun z=>projection (baseChart.symm z)) (τ:ℂ) := by
    have h := covering.continuous.continuousAt.comp (baseChart.symm.continuousAt hat)
    exact h
  have hp : Tendsto (fun z=>projection (baseChart.symm z)) (𝓝 (τ:ℂ))
      (𝓝 (projection τ)) := by simpa only [heτ] using hc
  have hs := (shift_locally_constant a b (projection τ) hqa hb).comp_tendsto hp
  have ht := (baseChart.symm.continuousAt hat).eventually
    (by rw [heτ];exact (chart a).open_target.mem_nhds ha)
  apply ((rawScalar_analytic (shift a b (projection τ)) τ τ.property).inv
    (rawScalar_ne _ τ τ.property)).congr
  filter_upwards [hs,ht,baseChart.open_target.mem_nhds hat] with z hz hzt hzu
  have hleft : chart a (projection (baseChart.symm z))=baseChart.symm z := by
    have h := (chart a).right_inv hzt
    simpa only [chart,IsLocalHomeomorph.localInverseAt_symm] using h
  have hcoe : ((baseChart.symm z:HalfPlane):ℂ)=z := baseChart.right_inv hzu
  simp only [transition,hz,hleft,←rawScalar_eq,hcoe]
end PELOriginalHolomorphicDeterminantTransitions318
