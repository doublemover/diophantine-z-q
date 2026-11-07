module
public import RegisteredLine318
public import HolomorphicInverse318
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DerivativeCocycle318 QuadraticFiber318 ContinuousDescent318 FiberQuotientCovering318
open LocalFrameEmbedding318 LocalTrivialization318 FrameTransition318 DependentFiberBundle318
open FiberLinearStructure318 VectorBundleRegistration318 HolomorphicCharts318 CotangentTransition318
open Filter Topology Bundle
open scoped Manifold ContDiff
namespace HolomorphicLineFactor318
set_option maxHeartbeats 0

@[expose] def factor (N:ℕ) (hN:5≤N) (a c:UpperHalfPlane) (b:Base (image N)) : ℂ :=
  ((deriv ((localChart N hN a).symm.trans (localChart N hN c))
    (localChart N hN a b))⁻¹)^2

theorem chart_source (N:ℕ) (hN:5≤N) (a:UpperHalfPlane) :
    (localChart N hN a).source=sheet N hN a := by
  ext b
  change (b∈sheet N hN a ∧ ((quotient_localHomeomorph N hN).localInverseAt a b)∈ofComplex.symm.source) ↔ b∈sheet N hN a
  change (b∈sheet N hN a ∧ ((quotient_localHomeomorph N hN).localInverseAt a b)∈Set.univ) ↔ b∈sheet N hN a
  simp

theorem chart_transition_mem (N:ℕ) (hN:5≤N) (a c:UpperHalfPlane)
    (b:Base (image N)) (hb:b∈sheet N hN a∩sheet N hN c) :
    localChart N hN a b∈((localChart N hN a).symm.trans (localChart N hN c)).source := by
  have ha:b∈(localChart N hN a).source:=by rw [chart_source];exact hb.1
  constructor
  · exact (localChart N hN a).map_source ha
  · change (localChart N hN a).symm (localChart N hN a b)∈(localChart N hN c).source
    rw [(localChart N hN a).left_inv ha,chart_source]
    exact hb.2

/-- The actual inverse derivative-square cocycle is holomorphic as a function
on the genuine quotient manifold, not merely in an abstract parameter. -/
theorem factor_holomorphic (N:ℕ) (hN:5≤N) (a c:UpperHalfPlane) :
    letI:=complexChartedSpace N hN
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (factor N hN a c) (sheet N hN a∩sheet N hN c) := by
  letI:=complexChartedSpace N hN
  have hi:=HolomorphicInverse318.localInverseAt_holomorphic N hN a
  have hc:ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localChart N hN a) (sheet N hN a) := by
    exact UpperHalfPlane.contMDiff_coe.comp_contMDiffOn hi
  have hf:ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z:ℂ=>((deriv ((localChart N hN a).symm.trans (localChart N hN c)) z)⁻¹)^2)
      ((localChart N hN a).symm.trans (localChart N hN c)).source := by
    exact ((analytic_cotangent_factor N hN a c).contDiffOn
      ((localChart N hN a).symm.trans (localChart N hN c)).open_source.uniqueDiffOn).contMDiffOn
  exact hf.comp (hc.mono Set.inter_subset_left) (chart_transition_mem N hN a c)

end HolomorphicLineFactor318
