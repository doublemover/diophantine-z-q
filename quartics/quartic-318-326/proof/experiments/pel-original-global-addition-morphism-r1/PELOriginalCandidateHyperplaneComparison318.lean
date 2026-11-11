module
public import LineCoreHomeomorphPullback318
public import PELOriginalHyperplanePullbackHolomorphy318
public import PELOriginalCandidateHomeomorph318
public import PELOriginalCandidateSmooth318
public section
noncomputable section
namespace PELOriginalCandidateHyperplaneComparison318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationPowerBundle318
open PELOriginalCandidateHomeomorph318 PELOriginalHyperplanePullback318
open PELOriginalHyperplanePullbackTopology318 PELOriginalHyperplanePullbackHolomorphy318
open ComplexProjectiveQuotientTopology318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance targetTopology : TopologicalSpace (Space (Label 3)) := topology (Label 3)

/-- The actual ambient dual-tautological cocycle restricted to the FULL
independent projective candidate. It is defined from the ambient inclusion,
not from the original line bundle or a transported bundle structure. -/
@[expose] def candidateCore : VectorBundleCore ℂ (CandidatePoints τ hτ) ℂ (Label 3) :=
  LineCoreHomeomorphPullback318.core (ComplexProjectiveHyperplaneBundle318.core (Label 3))
    Subtype.val continuous_subtype_val
abbrev CandidateFiber (p : CandidatePoints τ hτ) := (candidateCore τ hτ).Fiber p
abbrev CandidateTotal := (candidateCore τ hτ).TotalSpace
instance : FiberBundle ℂ (CandidateFiber τ hτ) := (candidateCore τ hτ).fiberBundle
instance : VectorBundle ℂ ℂ (CandidateFiber τ hτ) := (candidateCore τ hτ).vectorBundle

/-- The original cubic power line bundle and the actual hyperplane line
on the whole candidate have homeomorphic total spaces over the SAME
original comparison. No denominator subset remains in this statement. -/
@[expose] def comparisonTotal : PowerTotal τ hτ 3 ≃ₜ CandidateTotal τ hτ :=
  (PELOriginalHyperplanePullbackTopology318.homeomorph τ hτ 1).trans
    (LineCoreHomeomorphPullback318.homeomorph (candidateCore τ hτ) (comparison τ hτ))

lemma comparison_base (p : PowerTotal τ hτ 3) :
    (comparisonTotal τ hτ p).1 = comparison τ hτ p.1 := rfl

/-- The map is linear on each original fiber, with the exact section
normalization already fixed by the original theta map. -/
@[expose] def fiberComparison (q : Base τ) :
    PowerFiber τ hτ 3 q ≃ₗ[ℂ] CandidateFiber τ hτ (comparison τ hτ q) :=
  fiberEquivalence τ hτ 1 q

lemma comparison_fiber (q : Base τ) (v : PowerFiber τ hτ 3 q) :
    comparisonTotal τ hτ ⟨q,v⟩ = ⟨comparison τ hτ q,fiberComparison τ hτ q v⟩ := rfl

/-- The target fiber is identified with the true dual of the ACTUAL
projective tautological line, fixing the O(1), rather than O(-1), sign. -/
@[expose] def fiberDual (p : CandidatePoints τ hτ) :
    CandidateFiber τ hτ p ≃ₗ[ℂ] (p.val.submodule →ₗ[ℂ] ℂ) :=
  ComplexProjectiveHyperplaneBundle318.fiberDual (Label 3) p.val

/-- Exact formula on every genuine original/candidate bundle overlap:
no unspecified transition unit is substituted for the actual cubic. -/
lemma candidate_coordinate (a : ComplexVectors) (j : Label 3)
    (p : PowerTotal τ hτ 3) (ha : p.1 ∈ baseSet τ hτ a)
    (hj : (comparison τ hτ p.1).val ∈ domain (Label 3) j) :
    ((candidateCore τ hτ).localTriv j (comparisonTotal τ hτ p)).2 =
      ((powerCore τ hτ 3).localTriv a p).2 /
        value τ hτ 3 j (chart τ hτ a p.1) := by
  change ((pullbackCore τ hτ 1).localTriv j
    (PELOriginalHyperplanePullbackTopology318.homeomorph τ hτ 1 p)).2 = _
  rw [original_chart_ratio τ hτ 1 a p.1 ha j hj p.2]
  rw [←coefficient_original τ hτ 1 a j p.1 ha]
  rfl

/-- Both exact bundle coordinate maps are holomorphic everywhere on
those overlaps. This is a full original polarized analytic bundle
comparison; algebraic twisting-sheaf descent remains a separate interface. -/
theorem local_biholomorphy (a : ComplexVectors) (j : Label 3)
    (p : PowerTotal τ hτ 3) (ha : p.1 ∈ baseSet τ hτ a)
    (hj : (comparison τ hτ p.1).val ∈ domain (Label 3) j) :
    DifferentiableAt ℂ (forwardLocal τ hτ 1 j) (originalCoordinates τ hτ 1 a p) ∧
    DifferentiableAt ℂ (inverseLocal τ hτ 1 j)
      (pullbackCoordinates τ hτ 1 a j
        (PELOriginalHyperplanePullbackTopology318.homeomorph τ hτ 1 p)) :=
  actual_local_biholomorphy τ hτ 1 a j p ha hj
end PELOriginalCandidateHyperplaneComparison318
