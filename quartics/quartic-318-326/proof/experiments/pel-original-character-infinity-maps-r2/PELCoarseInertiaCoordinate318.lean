module
public import ComplexFixedInvolutionCoordinate318
public section
noncomputable section
namespace PELCoarseInertiaCoordinate318
open QuaternionicJointPeriodTopology318 PELJointComplexAtlas318 PELPrincipalBaseHolomorphy318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318 PELUnlevelledNormalizerAction318
open PELUnlevelledComplexBase318 PELQuaternionAlgebra318 PELQuaternionRealRepresentation318
open QuaternionicFixedParameter318 PELPrincipalThreeStabilizer318 ComplexTwoPointCoordinate318
open ComplexFixedInvolutionCoordinate318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1800000
local instance : ChartedSpace ℂ HalfPlane := halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := halfPlane_manifold

@[expose] def localLift (τ : HalfPlane) : OpenPartialHomeomorph UnlevelledBase HalfPlane :=
  covering.isLocalHomeomorph.localInverseAt τ

@[expose] def inertiaChart (τ : HalfPlane) : OpenPartialHomeomorph UnlevelledBase ℂ :=
  ((localLift τ).trans baseChart).trans
    (chart (τ:ℂ) (star (τ:ℂ)) (upper_ne_conjugate τ τ τ.property τ.property))

theorem lift_center (τ : HalfPlane) : localLift τ (projection τ)=τ := by
  have ht : τ∈(localLift τ).target := covering.isLocalHomeomorph.self_mem_localInverseAt_target
  have h := (localLift τ).right_inv ht
  rwa [localLift,covering.isLocalHomeomorph.localInverseAt_symm] at h

theorem lift_center_source (τ : HalfPlane) : projection τ∈(localLift τ).source := by
  have ht : τ∈(localLift τ).target := covering.isLocalHomeomorph.self_mem_localInverseAt_target
  have h := (localLift τ).map_target ht
  rwa [localLift,covering.isLocalHomeomorph.localInverseAt_symm] at h

theorem chart_value (τ : HalfPlane) (x : UnlevelledBase) :
    inertiaChart τ x=coordinate (τ:ℂ) (star (τ:ℂ)) (localLift τ x:ℂ) := rfl

theorem chart_center_source (τ : HalfPlane) : projection τ∈(inertiaChart τ).source := by
  change (projection τ∈(localLift τ).source ∧ localLift τ (projection τ)∈baseChart.source) ∧
    baseChart (localLift τ (projection τ))≠star (τ:ℂ)
  rw [lift_center,baseChart_value]
  exact ⟨⟨lift_center_source τ,baseChart_source τ⟩,upper_ne_conjugate τ τ τ.property τ.property⟩

theorem chart_center (τ : HalfPlane) : inertiaChart τ (projection τ)=0 := by
  rw [chart_value,lift_center,coordinate_center]

/-- The local inverse branch is compatible with the actual fixed action
on a genuine open neighborhood, not merely on isolated representatives. -/
theorem local_lift_action (g : positiveNormalizer) (τ : HalfPlane) (hfix : baseAction g τ=τ) :
    (fun x => localLift τ (coarseAction g x)) =ᶠ[𝓝 (projection τ)]
      (fun x => baseAction g (localLift τ x)) := by
  let C := localLift τ
  have hs : projection τ∈C.source := lift_center_source τ
  have ht : τ∈C.target := covering.isLocalHomeomorph.self_mem_localInverseAt_target
  have hC : ContinuousAt C (projection τ) := C.continuousOn.continuousAt (C.open_source.mem_nhds hs)
  have hCt : Tendsto C (𝓝 (projection τ)) (𝓝 τ) := by
    change Tendsto C (𝓝 (projection τ)) (𝓝 (C (projection τ))) at hC
    rwa [lift_center] at hC
  have hg : Tendsto (fun x => baseAction g (C x)) (𝓝 (projection τ)) (𝓝 τ) := by
    have hng : Tendsto (baseAction g) (𝓝 τ) (𝓝 (baseAction g τ)) :=
      (baseAction_holomorphic g τ).continuousAt
    have hgc := hng.comp hCt
    rwa [hfix] at hgc
  filter_upwards [C.open_source.mem_nhds hs,hg.eventually (C.open_target.mem_nhds ht)] with x hx hgx
  have hxq : projection (C x)=x := by
    have he := C.left_inv hx
    rwa [localLift,covering.isLocalHomeomorph.localInverseAt_symm] at he
  have he := C.right_inv hgx
  rw [localLift,covering.isLocalHomeomorph.localInverseAt_symm] at he
  rw [←coarseAction_square,hxq] at he
  exact he

/-- A genuine original local chart linearizes the actual trace-zero fixed
coarse automorphism to sign change on an OPEN neighborhood. -/
theorem local_negation (g : positiveNormalizer) (τ : HalfPlane)
    (hfix : baseAction g τ=τ) (htrace : reducedTrace (g.val:B)=0) :
    (fun x => inertiaChart τ (coarseAction g x)) =ᶠ[𝓝 (projection τ)]
      (fun x => -inertiaChart τ x) := by
  have hline := fixesLine_of_mobius (PELPositiveNormalizerMobius318.matrix g) τ
    (QuaternionicPositiveDeterminant318.denominator_nonzero _ (matrix_positive g) τ τ.property)
    (congrArg Subtype.val hfix)
  have ht : PELPositiveNormalizerMobius318.matrix g 0 0+
      PELPositiveNormalizerMobius318.matrix g 1 1=0 := by
    change representation (g.val:B) 0 0+representation (g.val:B) 1 1=0
    rw [representation_trace,htrace] <;> norm_num
  filter_upwards [local_lift_action g τ hfix] with x hx
  rw [chart_value,chart_value,hx]
  exact original_negation _ (matrix_positive g) τ (localLift τ x) τ.property
    (localLift τ x).property hline ht
end PELCoarseInertiaCoordinate318
