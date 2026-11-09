module
public import ActualFivePullbackEquivalence318
public import Mathlib.Algebra.DirectSum.Module

public section
noncomputable section
namespace ActualFivePullbackDirectSum318
open ActualFiveRationalIndependent318 ActualQuotientDifferentialLinear318
open ActualFivePullbackEquivalence318
open scoped BigOperators DirectSum
attribute [local instance] rationalModule characterModule fifthModule targetModule
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine module direct sum of all five actual target differential spaces. -/
abbrev SumSpace := ⨁ i : Index, TargetSpace i

@[expose] def sumMap : SumSpace →ₗ[ℚ] G :=
  DirectSum.toModule ℚ Index G pullback

theorem sumMap_component (i : Index) (s : TargetSpace i) :
    sumMap (DirectSum.lof ℚ Index TargetSpace i s) = pullback i s :=
  DirectSum.toModule_lof ℚ i s

theorem sumPullback_single (i : Index) (s : TargetSpace i) :
    sumPullback (Pi.single i s) = pullback i s := by
  change (∑ j, pullback j (Pi.single i s j)) = _
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

/-- The coproduct universal map is exactly the finite sum, not merely isomorphic. -/
theorem sumMap_eq : sumMap = sumPullback.comp
    (DirectSum.linearEquivFunOnFintype ℚ Index TargetSpace).toLinearMap := by
  apply DirectSum.linearMap_ext
  intro i
  ext s
  change sumMap (DirectSum.lof ℚ Index TargetSpace i s) =
    sumPullback ((DirectSum.linearEquivFunOnFintype ℚ Index TargetSpace)
      (DirectSum.lof ℚ Index TargetSpace i s))
  rw [sumMap_component, DirectSum.linearEquivFunOnFintype_lof, sumPullback_single]

/-- Actual direct-sum pullback equivalence, including every original quotient. -/
@[expose] def equivalence : SumSpace ≃ₗ[ℚ] G :=
  (DirectSum.linearEquivFunOnFintype ℚ Index TargetSpace).trans
    ActualFivePullbackEquivalence318.equivalence

theorem equivalence_toLinearMap : equivalence.toLinearMap = sumMap := by
  exact sumMap_eq.symm

theorem equivalence_component (i : Index) (s : TargetSpace i) :
    equivalence (DirectSum.lof ℚ Index TargetSpace i s) = pullback i s := by
  change equivalence.toLinearMap _ = _
  rw [equivalence_toLinearMap, sumMap_component]

theorem sumMap_bijective : Function.Bijective sumMap := by
  rw [← equivalence_toLinearMap]
  exact equivalence.bijective

end ActualFivePullbackDirectSum318
