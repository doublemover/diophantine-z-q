module
public import HolomorphicLineRegistration318
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DependentFiberBundle318 FiberLinearStructure318 VectorBundleRegistration318
open HolomorphicCharts318 HolomorphicLineFactor318 LinearCocycleBinding318
open LocalFrameEmbedding318
open Filter Topology Bundle
open scoped Manifold ContDiff
namespace TangentCoordinates318
set_option maxHeartbeats 0
variable (N:ℕ) [hN:Fact (5≤N)]
local instance quotientCharts : ChartedSpace ℂ (Base (image N)) := complexChartedSpace N hN.out
local instance quotientManifold : IsManifold 𝓘(ℂ) ω (Base (image N)) := complex_manifold N hN.out

@[expose] def atlasChart (a:UpperHalfPlane) : atlas ℂ (Base (image N)) :=
  ⟨localChart N hN.out a,⟨a,rfl⟩⟩

/-- The actual Mathlib tangent coordinate change is multiplication by the
actual complex chart-transition derivative. -/
theorem tangent_change (a c:UpperHalfPlane) (b:Base (image N)) (v:ℂ) :
    (tangentBundleCore 𝓘(ℂ) (Base (image N))).coordChange
      (atlasChart N a) (atlasChart N c) b v=
      deriv ((localChart N hN.out a).symm.trans (localChart N hN.out c))
        (localChart N hN.out a b)*v := by
  simp only [tangentBundleCore_coordChange,OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    fderivWithin_univ]
  exact fderiv_eq_deriv_mul

@[expose] def tangentFrame (a:UpperHalfPlane) :=
  (tangentBundleCore 𝓘(ℂ) (Base (image N))).localTriv (atlasChart N a)

/-- The actual tangent trivialization, in the chosen pointwise tangent model,
uses the derivative from the preferred quotient chart to the given chart. -/
theorem tangent_frame_apply (a:UpperHalfPlane) (b:Base (image N))
    (v:TangentSpace 𝓘(ℂ) b) :
    tangentFrame N a ⟨b,v⟩=(b,
      deriv ((localChart N hN.out (chosenLift N b)).symm.trans (localChart N hN.out a))
        (localChart N hN.out (chosenLift N b) b)*(show ℂ from v)) := by
  rw [tangentFrame,VectorBundleCore.localTriv_apply]
  congr 1
  exact tangent_change N (chosenLift N b) a b v

end TangentCoordinates318
