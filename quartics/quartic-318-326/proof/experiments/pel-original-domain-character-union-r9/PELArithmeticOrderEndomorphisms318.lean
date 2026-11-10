module
public import PELJointOrderEndomorphisms318
public section
noncomputable section
namespace PELArithmeticOrderEndomorphisms318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318 QuaternionicJointPeriodTopology318
open PELJointPeriodFamily318 PELJointPeriodDeck318 PELJointComplexAtlas318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318 PELComplexPeriodSurface318
open PELPrincipalThreeFreeAction318 PELPrincipalProperAction318 PELPrincipalThreeCovering318
open PELArithmeticComplexFamily318 PELArithmeticOriginalFibers318 PELJointOrderEndomorphisms318
open HolomorphicQuotientCoverMaps318
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000

/-- Literal descent of each original integral-order endomorphism through
the original arithmetic orbit relation. -/
@[expose] def arithmeticOrder (a : order) : ArithmeticTotal → ArithmeticTotal :=
  Quotient.map' (jointOrder a) (by
    rintro p q ⟨u,hu⟩
    refine ⟨u,?_⟩
    rw [←jointOrder_commutes,hu])

theorem arithmeticOrder_square (a : order) (p : Total) :
    arithmeticOrder a (totalQuotient p)=totalQuotient (jointOrder a p) := rfl

theorem arithmeticOrder_over_base (a : order) (p : ArithmeticTotal) :
    arithmeticProjection (arithmeticOrder a p)=arithmeticProjection p := by
  obtain ⟨x,rfl⟩ := totalQuotient_surjective p
  all_goals rfl

local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold
local instance : ChartedSpace Ambient ArithmeticTotal := arithmeticTotalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω ArithmeticTotal := arithmeticTotal_manifold

/-- Original quaternionic endomorphisms are holomorphic on the entire
arithmetic family, with both quotient maps and all representatives checked. -/
theorem arithmeticOrder_holomorphic (a : order) :
    ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,Ambient) ω (arithmeticOrder a) :=
  descended_holomorphic totalQuotient total_covering principal_total_holomorphic
    (arithmeticOrder a) (fun p => totalQuotient (jointOrder a p))
    (totalQuotient_holomorphic.comp (jointOrder_holomorphic a)) (arithmeticOrder_square a)

@[expose] def fiberOrder (τ : HalfPlane) (a : order) : ArithmeticFiber τ → ArithmeticFiber τ :=
  fun p => ⟨arithmeticOrder a p.val,(arithmeticOrder_over_base a p.val).trans p.property⟩

/-- Exact original-order compatibility on every full arithmetic fiber.
This is not an endomorphism of an unrelated isomorphic torus. -/
theorem original_fiber_order (τ : HalfPlane) (a : order) (p : Surface τ) :
    fiberOrder τ a (originalFiberEquiv τ p)=
      originalFiberEquiv τ (orderEnd representation order τ a p) := by
  apply Subtype.ext
  change arithmeticOrder a (totalQuotient (τ,fiberEquiv τ p))=
    totalQuotient (τ,fiberEquiv τ (orderEnd representation order τ a p))
  rw [arithmeticOrder_square,jointOrder_original_fiber]

/-- The original period coordinates survive the arithmetic-order action
for every vector, not just torsion or lattice representatives. -/
theorem original_period_order (a : order) (τ : HalfPlane) (z : ComplexVectors) :
    arithmeticOrder a (totalQuotient (familyProjection (τ,z)))=
      totalQuotient (familyProjection (τ,leftLinear (representation a) z)) := by
  rw [arithmeticOrder_square,jointOrder_square]
  all_goals rfl
end PELArithmeticOrderEndomorphisms318
