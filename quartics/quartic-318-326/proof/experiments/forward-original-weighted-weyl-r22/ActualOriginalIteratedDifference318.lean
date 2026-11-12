module
public import ActualOriginalSmoothCompleteTwoAxis318
public section
noncomputable section
namespace ActualOriginalIteratedDifference318

/-- Ordered finite differences; the function and all actual points stay
unchanged. This definition applies also to operator-valued derivatives. -/
@[expose] def mixedDifference {E F : Type*} [Add E] [Sub F]
    (f : E → F) : List E → E → F
  | [], x => f x
  | u::us, x => mixedDifference f us (x+u)-mixedDifference f us x

@[expose] def directionProduct {E : Type*} [Norm E] : List E → ℝ
  | [] => 1
  | u::us => ‖u‖*directionProduct us

lemma actual_direction_product_nonneg {E : Type*} [Norm E]
    (hn : ∀ u : E, 0≤‖u‖) (us : List E) : 0≤directionProduct us := by
  induction us with
  | nil => exact zero_le_one
  | cons u us ih => exact mul_nonneg (hn u) ih

/-- Differentiation commutes with the actual finite translation/subtraction
expression, with no claimed exchange of an infinite sum or limit. -/
theorem actual_mixed_hasFDerivAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : Differentiable ℝ f) (us : List E) :
    ∀ x, HasFDerivAt (mixedDifference f us)
      (mixedDifference (fderiv ℝ f) us x) x := by
  induction us with
  | nil => intro x; exact (hf x).hasFDerivAt
  | cons u us ih =>
    intro x
    have ht := (ih (x+u)).comp x ((hasFDerivAt_id x).add_const u)
    simpa only [mixedDifference,ContinuousLinearMap.comp_id] using ht.sub (ih x)

end ActualOriginalIteratedDifference318
