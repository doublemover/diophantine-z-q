module
public import OriginalPeriodIndependentHolomorphy318
public import ComplexCurveOpenMapping318
public import Mathlib.Topology.Homeomorph.Lemmas
public section
noncomputable section
namespace OriginalPeriodIndependentBiholomorph318
open OriginalPeriodCompletedPointIdentification318 OriginalPeriodPlaneOverlap318
open OriginalPeriodIndependentContinuity318 OriginalPeriodIndependentHolomorphy318
open ComplexAffineFreeTranslation318 Set
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 2600000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
local instance : ChartedSpace ℂ (Torus L) := ComplexLineLatticeAtlas318.chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Torus L) := ComplexLineLatticeAtlas318.complex_manifold L
local instance : ChartedSpace ℂ (CompletedPlane L) := OriginalPeriodCompletedComplexAtlas318.chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CompletedPlane L) := OriginalPeriodCompletedComplexAtlas318.complex_manifold L

/-- The actual holomorphic point bijection is OPEN in the independent
polynomial target topology. This is complex open mapping, not a compact
bijection argument that would silently require an unproved target T2. -/
theorem original_open : IsOpenMap (originalPoint L) :=
  ComplexCurveOpenMapping318.isOpenMap (originalPoint L) (original_holomorphic L)
    Set.univ isOpen_univ dense_univ (fun _ _ _ _ h=>(original_bijective L).1 h)

/-- The same original coordinate map is a homeomorphism to the completed
curve with its INDEPENDENT two-chart polynomial topology. -/
@[expose] def comparison : Torus L ≃ₜ CompletedPlane L :=
  (Equiv.ofBijective (originalPoint L) (original_bijective L)).toHomeomorphOfContinuousOpen
    (original_continuous L) (original_open L)
lemma comparison_value (q : Torus L) : comparison L q=originalPoint L q := rfl

/-- Actual inverse holomorphy is derived on both original atlases from
injective analytic chart germs. No inverse holomorphy or derivative is
supplied, and no target complex structure is transported from the torus. -/
theorem biholomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison L) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (comparison L).symm :=
  ⟨original_holomorphic L,
    ComplexCurveHomeomorphInverse318.inverse (comparison L) (original_holomorphic L)⟩

/-- The global analytic comparison retains the PREVIOUS actual map to
ALL actual complex scheme-valued points of the original projective cubic. -/
lemma actual_scheme (q : Torus L) : schemeEquivalence L (comparison L q)=
    OriginalPeriodCompletedSchemeBijection318.point L q := original_scheme L q
lemma actual_origin : comparison L 0=infinityChart L (origin L) := original_zero L
lemma actual_finite (q : Torus L) (hq : q≠0) :
    comparison L q=finiteChart L (originalFinite L ⟨q,hq⟩) := original_nonzero L q hq
end OriginalPeriodIndependentBiholomorph318
