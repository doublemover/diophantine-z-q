module
public import OriginalFifthPullbackLine318
public import ActualFiveHOneRationalExhaustion318

public section
noncomputable section
namespace OriginalFivePullbackIndependence318
open ActualFiveHOneDecomposition318 ActualFiveHOneRationalExhaustion318
open ActualSourceHOnePullbacks318
open ActualSourceHOneCharacterAction318 ActualSourceHOneCharacterProjectors318
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- All five original pullbacks have been placed in their exact original character lines. -/
theorem pullback_line (i : Index) (x : TargetHOne i) :
    ∃ q : ℚ, pullback i x = q • characterClass i := by
  cases i with
  | none => exact OriginalFifthPullbackLine318.pullback_line x
  | some i => exact OriginalCharacterPullbackLines318.pullback_line i x

/-- The actual geometric character projectors separate the original five quotient images. -/
theorem projector_pullback (i j : Index) (x : TargetHOne j) :
    projector i (pullback j x) = if i = j then pullback j x else 0 := by
  obtain ⟨q,hq⟩ := pullback_line j x
  rw [hq,map_smul,projector_characterClass]
  by_cases hij : i = j <;> simp only [hij,ite_true,ite_false,smul_zero]

/-- Projecting the original five-map sum recovers each original pullback separately. -/
theorem projector_sumPullback (i : Index) (x : (j : Index) → TargetHOne j) :
    projector i (sumPullback x) = pullback i (x i) := by
  classical
  change projector i (∑ j, pullback j (x j)) = _
  simp only [map_sum,projector_pullback]
  simp

/-- Unconditional independence of the original five quotient-H1 images.
No cross-transfer equation or nonzero-target assumption is used. -/
theorem sumPullback_injective : Function.Injective sumPullback := by
  intro x y hxy
  funext i
  apply Function.LeftInverse.injective (split i)
  have h := congrArg (projector i) hxy
  simpa only [projector_sumPullback] using h

theorem sumLinear_injective : Function.Injective sumLinear := sumPullback_injective

/-- With target nonvanishing supplied, dimension exhaustion no longer needs any cross-transfer hypothesis. -/
theorem sumLinear_surjective (hnonzero : TargetsNonzero) : Function.Surjective sumLinear := by
  have hle := LinearMap.finrank_le_finrank_of_injective sumLinear_injective
  have hge := target_product_finrank_ge_five hnonzero
  have hsource := ActualSourceHOneResidueBasis318.source_finrank_eq_five
  have heq : Module.finrank ℚ ((i : Index) → TargetHOne i) = Module.finrank ℚ SourceHOne := by
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp sumLinear_injective

/-- The forward map is the original five-pullback sum. Target nonvanishing is still an explicit input.
This does not assert that the inverse is the original vector of normalized transfers. -/
@[expose] def actualEquivalence (hnonzero : TargetsNonzero) :
    ((i : Index) → TargetHOne i) ≃ₗ[ℚ] SourceHOne :=
  LinearEquiv.ofBijective sumLinear ⟨sumLinear_injective,sumLinear_surjective hnonzero⟩

theorem actualEquivalence_apply (hnonzero : TargetsNonzero) (x : (i : Index) → TargetHOne i) :
    actualEquivalence hnonzero x = ∑ i, pullback i (x i) := rfl

end OriginalFivePullbackIndependence318
