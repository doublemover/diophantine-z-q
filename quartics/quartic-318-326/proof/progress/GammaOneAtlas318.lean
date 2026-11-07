module
public import GammaOneProper318
public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Mathlib.Geometry.Manifold.HasGroupoid
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 PeterssonQuotient318
namespace GammaOneAtlas318
set_option maxHeartbeats 0

/-- The genuine orbit projection of the actual fine-level group. -/
@[expose] def quotientMap (N:ℕ) : UpperHalfPlane→Base (image N) :=
  Quotient.mk (MulAction.orbitRel (image N) UpperHalfPlane)

/-- Actual quotient-covering structure, including disjoint sheets. -/
theorem quotient_covering (N:ℕ) (hN:5≤N) :
    IsQuotientCoveringMap (quotientMap N) (image N) := by
  letI:Fact (5≤N):=⟨hN⟩
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The actual fine-level orbit projection is a local homeomorphism. -/
theorem quotient_localHomeomorph (N:ℕ) (hN:5≤N) :
    IsLocalHomeomorph (quotientMap N) := (quotient_covering N hN).isLocalHomeomorph

theorem quotient_surjective (N:ℕ) : Function.Surjective (quotientMap N) :=
  Quotient.mk_surjective

/-- The actual orbit quotient is Hausdorff, not only a set quotient. -/
theorem quotient_hausdorff (N:ℕ) : T2Space (Base (image N)) := inferInstance

/-- A genuine complex-coordinate topological atlas on the actual quotient.
This does not yet assert holomorphic transition maps. -/
@[expose, instance_reducible] def chartedSpace (N:ℕ) (hN:5≤N) : ChartedSpace ℂ (Base (image N)) := by
  letI:ChartedSpace ℂ UpperHalfPlane:=isOpenEmbedding_coe.singletonChartedSpace
  exact (quotient_localHomeomorph N hN).chartedSpace (quotient_surjective N)

/-- Every actual quotient point lies in the source of an actual complex-coordinate chart. -/
theorem exists_chart (N:ℕ) (hN:5≤N) (q:Base (image N)) :
    ∃e:OpenPartialHomeomorph (Base (image N)) ℂ, q∈e.source := by
  letI:=chartedSpace N hN
  exact ⟨chartAt ℂ q,mem_chart_source ℂ q⟩
end GammaOneAtlas318
