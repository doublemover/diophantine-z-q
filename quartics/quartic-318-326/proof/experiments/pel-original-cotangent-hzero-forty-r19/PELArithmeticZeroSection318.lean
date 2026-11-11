module
public import PELArithmeticOrderEndomorphisms318
public section
noncomputable section
namespace PELArithmeticZeroSection318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318
open PELJointPeriodFamily318 PELJointPeriodDeck318 PELJointComplexAtlas318
open PELHolomorphicFamilyProjection318 PELOriginalHolomorphicFibers318
open PELJointArithmeticLift318 PELPrincipalThreeFreeAction318 PELPrincipalProperAction318
open PELPrincipalThreeCovering318 PELPrincipalBaseHolomorphy318 PELArithmeticComplexFamily318
open HolomorphicQuotientCoverMaps318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000

@[expose] def jointZero (τ : HalfPlane) : Total := (τ,0)
@[expose] def zeroLinear : ℂ →ₗ[ℂ] Ambient where
  toFun z := (z,0)
  map_add' x y := by simp
  map_smul' c x := by simp

theorem zero_projection (τ : HalfPlane) : familyProjection (τ,0)=jointZero τ := by
  rw [projection_fiber,map_zero,map_zero]
  all_goals rfl

theorem zero_inverse_chart (a : Cover) (τ : HalfPlane) :
    (familyChart a).symm (zeroLinear (τ:ℂ))=jointZero τ := by
  rw [familyChart_symm]
  have h : ambientChart.symm (zeroLinear (τ:ℂ))=(τ,(0:ComplexVectors)) :=
    ambientChart.left_inv (ambientChart_source (τ,0))
  rw [h,zero_projection]

local instance : ChartedSpace ℂ HalfPlane := halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := halfPlane_manifold
local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold

theorem jointZero_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Ambient) ω jointZero := by
  intro τ
  have ht : zeroLinear (τ:ℂ)∈(familyChart (τ,0)).target := by
    have h := (familyChart (τ,0)).map_source (familyChart_center (τ,0))
    rwa [familyChart_at_center] at h
  have hi := contMDiffAt_symm_of_mem_maximalAtlas (familyChart_maximal (τ,0)) ht
  have hz : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,Ambient) ω zeroLinear (τ:ℂ) :=
    contMDiffAt_iff_contDiffAt.mpr zeroLinear.toContinuousLinearMap.contDiff.contDiffAt
  apply (hi.comp τ (hz.comp τ (inclusion_holomorphic τ))).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun σ => (zero_inverse_chart (τ,0) σ).symm)

theorem zero_equivariant (u : principalThree) (τ : HalfPlane) :
    u • jointZero τ=jointZero (u • τ) := by
  rw [←zero_projection τ,PELPrincipalThreeFreeAction318.projection_square]
  change familyProjection (nextParameter u.val (determinant u) τ,
    (QuaternionicUnitPeriodTransport318.unitDenominator
      PELQuaternionRealRepresentation318.representation PELPrincipalOrderCoordinates318.order u.val τ)⁻¹ •
      (0:ComplexVectors))=jointZero (u • τ)
  rw [smul_zero]
  exact zero_projection (u • τ)

/-- The zero section is descended through the SAME base orbit relation
using its actual arithmetic equivariance, rather than chosen fiberwise. -/
@[expose] def arithmeticZero : ArithmeticBase → ArithmeticTotal :=
  Quotient.lift (fun τ => totalQuotient (jointZero τ)) (by
    rintro τ σ ⟨u,hu⟩
    rw [←hu,←zero_equivariant,total_covering.map_smul])

theorem arithmeticZero_square (τ : HalfPlane) :
    arithmeticZero (baseQuotient τ)=totalQuotient (jointZero τ) := rfl

theorem arithmeticZero_section (p : ArithmeticBase) :
    arithmeticProjection (arithmeticZero p)=p := by
  obtain ⟨τ,rfl⟩ := baseQuotient_surjective p
  all_goals rfl

local instance : ChartedSpace ℂ ArithmeticBase := arithmeticBaseCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω ArithmeticBase := arithmeticBase_manifold
local instance : ChartedSpace Ambient ArithmeticTotal := arithmeticTotalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω ArithmeticTotal := arithmeticTotal_manifold

/-- The actual original zero section is holomorphic on the arithmetic
quotient base, and its section identity holds globally. -/
theorem arithmeticZero_holomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Ambient) ω arithmeticZero :=
  descended_holomorphic baseQuotient base_covering principal_base_holomorphic
    arithmeticZero (fun τ => totalQuotient (jointZero τ))
    (totalQuotient_holomorphic.comp jointZero_holomorphic) arithmeticZero_square
end PELArithmeticZeroSection318
