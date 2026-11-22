module
public import ActualGaussianWeberOriginalFieldFoundation318
public import ActualGaussianWeberActualPeriodInCoordinateField318
public section
noncomputable section

namespace ActualGaussianWeberNamedPositivePeriodLift318

open ActualGaussianComplexTorusKernel318
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberHenselianPointMap318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberFullTorsionInertia318
open ActualGaussianWeberFullCoordinateField318 ActualGaussianWeberAlgebraicClosureTorsion318
open ActualGaussianWeberActualPeriodInCoordinateField318

attribute [local instance] Classical.decEq

/-- With the actual original point instances, the displayed old
coordinate field is exactly the adjoin used by the strict-data
period receiver. No comparison field or choice of embedding enters. -/
theorem literal_old_period_field (n : ℕ) :
    fullField Ω n=IntermediateField.adjoin Base (divisionCoordinates Ω n) := rfl

/-- The period point actually descends to the original named field
through its designated closure embedding, not just an abstract
isomorphic adjoin. This is existence of this division point, not
yet its Gaussian primitivity. -/
theorem actual_positive_period_lifts_to_old_field (n : ℕ) (hn : 1<n) :
    ∃ P : WP (fullField Ω n), n • P=0 ∧
      coordinateHom (chosenClosureEmbedding.comp (algebraMap (fullField Ω n) Ω))
        (by norm_num : (2:ℂ)≠0) P =
          ActualLSGOriginalFullUniformization318.uniformization.point (V ((1:ℂ)/(n:ℂ))) := by
  have he : chosenClosureEmbedding.comp (algebraMap Base Ω)=complexEmbedding :=
    RingHom.ext extends_chosen_complex
  exact actual_positive_period_lifts Ω chosenClosureEmbedding he n hn
    (fullField Ω n) (literal_old_period_field n)

end ActualGaussianWeberNamedPositivePeriodLift318
