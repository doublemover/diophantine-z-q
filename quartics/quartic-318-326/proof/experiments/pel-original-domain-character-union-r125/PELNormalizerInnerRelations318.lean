module
public import PELNormalizerResidueFrobenius318
public section
noncomputable section
namespace PELNormalizerInnerRelations318
open PELOrderReductionThree318 PELNormalizerReductionAction318
open PELPrimeNormalizerRelations318
set_option maxHeartbeats 1800000

/-- The square of each finite normalizer action is the actual inner action
of its original norm-one square unit. It is not silently declared trivial. -/
theorem square_inner (i : Fin 4) (x : Reduction) :
    reductionEquiv i (reductionEquiv i x)=
      reduction (squareUnit i:PELPrincipalOrderCoordinates318.order)*x*
        reduction ((squareUnit i)⁻¹:PELPrincipalOrderCoordinates318.order) := by
  change forward i (forward i x)=
    reduction (PELPrincipalOrderCoordinates318.coordinatesEquiv (squareCoefficients i))*x*
      reduction (PELPrincipalOrderCoordinates318.coordinatesEquiv (squareInverseCoefficients i))
  rw [reduction_coordinates,reduction_coordinates]
  fin_cases i <;> ext <;>
    norm_num [forward,reduceCoordinates,squareCoefficients,squareInverseCoefficients] <;> ring

/-- The two composition orders differ by the explicitly constructed
original commutator unit. This is outer-action data, not a claimed commuting
four-generator action on the finite group. -/
theorem commutator_inner (i j : Fin 4) (x : Reduction) :
    reductionEquiv i (reductionEquiv j x)=
      reduction (commutatorUnit i j:PELPrincipalOrderCoordinates318.order)*
        reductionEquiv j (reductionEquiv i x)*
          reduction ((commutatorUnit i j)⁻¹:PELPrincipalOrderCoordinates318.order) := by
  change forward i (forward j x)=
    reduction (PELPrincipalOrderCoordinates318.coordinatesEquiv (commutatorCoefficients i j))*
      forward j (forward i x)*
        reduction (PELPrincipalOrderCoordinates318.coordinatesEquiv (commutatorCoefficients j i))
  rw [reduction_coordinates,reduction_coordinates]
  fin_cases i <;> fin_cases j <;> ext <;>
    norm_num [forward,reduceCoordinates,commutatorCoefficients] <;> ring
end PELNormalizerInnerRelations318
