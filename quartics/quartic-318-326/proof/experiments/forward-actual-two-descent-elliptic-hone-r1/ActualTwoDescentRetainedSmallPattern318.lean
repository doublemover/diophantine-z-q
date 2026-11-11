module
public import ActualTwoDescentBaselineSupport318
public section
noncomputable section
namespace ActualTwoDescentRetainedSmallPattern318
open ActualTwoDescentSmallPattern318 ActualTwoDescentPrimeLaplacian318
open ActualTwoDescentQ0CoreReplacement318 ActualTwoDescentIncidence318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- The first-twist incidence pattern survives the SAME final q0 change
used to make the second-twist core invertible. -/
theorem actual_small_pattern_retained (d : ℕ) (p p' : Index d → ℕ)
    (hfix : ∀ i : CoreIndex d, p' (some i)=p (some i))
    (hbits : ∀ i : CoreIndex d, edges p' (some i) none=edges p (some i) none)
    (hseven : (p' none : ZMod 12)=7) (H : Pattern d p) : Pattern d p' := by
  constructor
  · intro b i
    change edges p' (some (Sum.inl b)) (some (Sum.inr i))=incidence d b i
    rw [actual_fixed_core_edges p p' hfix]
    exact H.cross b i
  · intro i j
    change edges p' (some (Sum.inr i)) (some (Sum.inr j))=0
    rw [actual_fixed_core_edges p p' hfix]
    exact H.internal i j
  · intro i
    change edges p' (some (Sum.inr i)) none=0
    rw [hbits]
    exact H.to_q0 i
  · intro b
    change edges p' (some (Sum.inl b)) none=∑ i, incidence d b i
    rw [hbits]
    exact H.q0_at_beta b
  · intro i
    change (p' (some (Sum.inr i)) : ZMod 12)=1
    rw [hfix]
    exact H.typeI i
  · exact hseven

end ActualTwoDescentRetainedSmallPattern318
