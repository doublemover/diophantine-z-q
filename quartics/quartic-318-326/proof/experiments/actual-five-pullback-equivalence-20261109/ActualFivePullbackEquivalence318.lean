module
public import ActualQuotientDifferentialLinear318

public section
noncomputable section
namespace ActualFivePullbackEquivalence318
open ActualFiveRationalIndependent318 ActualQuotientDifferentialLinear318
open scoped BigOperators
attribute [local instance] rationalModule characterModule fifthModule targetModule
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The full finite product of the five actual quotient differential spaces. -/
abbrev ProductSpace := (i : Index) → TargetSpace i

/-- The sum of the five original canonical whole-scheme differential pullbacks. -/
@[expose] def sumPullback : ProductSpace →ₗ[ℚ] G where
  toFun s := ∑ i, pullback i (s i)
  map_add' s t := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' a s := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

/-- Coordinates use the five original normalized invariant differentials. -/
@[expose] def coordinates : ProductSpace ≃ₗ[ℚ] (Index → ℚ) where
  toFun s i := (frame i).symm (s i)
  invFun a i := frame i (a i)
  map_add' s t := by ext i; exact (frame i).symm.map_add _ _
  map_smul' a s := by ext i; exact (frame i).symm.map_smul a _
  left_inv s := by ext i; exact (frame i).apply_symm_apply _
  right_inv a := by ext i; exact (frame i).symm_apply_apply _

theorem pullback_coordinates (i : Index) (s : TargetSpace i) :
    pullback i s = (frame i).symm s • differential i := by
  rw [← pullback_frame, (frame i).apply_symm_apply]

/-- Exact comparison with the accepted source basis, with no factor inserted. -/
theorem sumPullback_eq (s : ProductSpace) :
    sumPullback s = ActualFiveDifferentialBasis318.basis.equivFun.symm (coordinates s) := by
  rw [Module.Basis.equivFun_symm_apply]
  change (∑ i, pullback i (s i)) = _
  apply Finset.sum_congr rfl
  intro i _
  rw [ActualFiveDifferentialBasis318.basis_apply]
  exact pullback_coordinates i (s i)

theorem sumPullback_bijective : Function.Bijective sumPullback := by
  have h : (sumPullback : ProductSpace → G) =
      (coordinates.trans ActualFiveDifferentialBasis318.basis.equivFun.symm : ProductSpace → G) := by
    funext s
    exact sumPullback_eq s
  rw [h]
  exact (coordinates.trans ActualFiveDifferentialBasis318.basis.equivFun.symm).bijective

/-- The actual sum of all five quotient differential pullbacks is a rational
linear equivalence. This is a curve-differential statement, not a Jacobian map. -/
@[expose] def equivalence : ProductSpace ≃ₗ[ℚ] G :=
  LinearEquiv.ofBijective sumPullback sumPullback_bijective

theorem equivalence_apply (s : ProductSpace) :
    equivalence s = ∑ i, pullback i (s i) := rfl

theorem inverse_apply (s : G) (i : Index) :
    equivalence.symm s i = frame i (ActualFiveDifferentialBasis318.basis.equivFun s i) := by
  have h : equivalence =
      coordinates.trans ActualFiveDifferentialBasis318.basis.equivFun.symm := by
    ext s
    exact sumPullback_eq s
  rw [h]
  rfl

/-- Every source section is uniquely the sum of five actual target pullbacks. -/
theorem existsUnique_decomposition (s : G) :
    ∃! t : ProductSpace, (∑ i, pullback i (t i)) = s := by
  exact ⟨equivalence.symm s, equivalence.apply_symm_apply s,
    fun t ht => equivalence.injective (ht.trans (equivalence.apply_symm_apply s).symm)⟩

end ActualFivePullbackEquivalence318
