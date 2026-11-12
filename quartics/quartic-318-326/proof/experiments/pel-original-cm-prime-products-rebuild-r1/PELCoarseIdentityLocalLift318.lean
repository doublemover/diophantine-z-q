module
public import QuaternionicLocalIdentityScalar318
public section
noncomputable section
namespace PELCoarseIdentityLocalLift318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicMobiusPeriods318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318 PELNormalizerArithmeticBase318
open PELUnlevelledNormalizerAction318 PELUnlevelledComplexBase318 PELPrincipalBaseHolomorphy318
open PELJointComplexAtlas318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1600000
local instance : ChartedSpace ℂ HalfPlane := halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := halfPlane_manifold

theorem local_base_identity (g : positiveNormalizer) (τ : HalfPlane)
    (hfix : baseAction g τ=τ) (hid : ∀ x,coarseAction g x=x) :
    baseAction g =ᶠ[𝓝 τ] id := by
  let C := covering.isLocalHomeomorph.localInverseAt τ
  have ht : τ∈C.target := covering.isLocalHomeomorph.self_mem_localInverseAt_target
  have hft : baseAction g τ∈C.target := by
    rw [hfix]
    exact ht
  filter_upwards [C.open_target.mem_nhds ht,
    (baseAction_holomorphic g τ).continuousAt.eventually (C.open_target.mem_nhds hft)] with σ hσ hfσ
  have hq : projection (baseAction g σ)=projection σ := by
    rw [←coarseAction_square,hid]
  have ha := C.right_inv hfσ
  have hb := C.right_inv hσ
  rw [covering.isLocalHomeomorph.localInverseAt_symm] at ha hb
  exact ha.symm.trans ((congrArg C hq).trans hb)

/-- The original open half-plane chart converts the actual local covering
identity to an ambient complex germ, retaining an OPEN neighborhood. -/
theorem local_complex_identity (g : positiveNormalizer) (τ : HalfPlane)
    (hfix : baseAction g τ=τ) (hid : ∀ x,coarseAction g x=x) :
    mobius (PELPositiveNormalizerMobius318.matrix g) =ᶠ[𝓝 (τ:ℂ)] id := by
  have hloc := local_base_identity g τ hfix hid
  have ht : (τ:ℂ)∈baseChart.target := baseChart.map_source (baseChart_source τ)
  have hi := contMDiffAt_symm_of_mem_maximalAtlas baseChart_maximal ht
  have hv : baseChart.symm (τ:ℂ)=τ := baseChart.left_inv (baseChart_source τ)
  have hp : ∀ᶠ z in 𝓝 (τ:ℂ),baseAction g (baseChart.symm z)=baseChart.symm z := by
    have hc := hi.continuousAt
    change Tendsto baseChart.symm (𝓝 (τ:ℂ)) (𝓝 (baseChart.symm (τ:ℂ))) at hc
    rw [hv] at hc
    exact hc.eventually hloc
  filter_upwards [hp,baseChart.open_target.mem_nhds ht] with z hz hzt
  have he := congrArg Subtype.val hz
  have hec : (baseChart.symm z:ℂ)=z := baseChart.right_inv hzt
  change mobius (PELPositiveNormalizerMobius318.matrix g) (baseChart.symm z:ℂ)=
    (baseChart.symm z:ℂ) at he
  rwa [hec] at he
end PELCoarseIdentityLocalLift318
