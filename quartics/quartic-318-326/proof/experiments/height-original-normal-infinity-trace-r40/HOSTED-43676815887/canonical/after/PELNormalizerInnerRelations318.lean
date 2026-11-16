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
        reduction (((squareUnit i)⁻¹:PELPrincipalOrderCoordinates318.orderˣ):PELPrincipalOrderCoordinates318.order) := by
  have h3 : (3:F3)=0 := by decide
  change forward i (forward i x)=
    reduction (PELPrincipalOrderCoordinates318.coordinatesEquiv (squareCoefficients i))*x*
      reduction (PELPrincipalOrderCoordinates318.coordinatesEquiv (squareInverseCoefficients i))
  rw [reduction_coordinates,reduction_coordinates]
  fin_cases i <;> ext <;>
    norm_num [forward,reduceCoordinates,squareCoefficients,squareInverseCoefficients] <;> ring
  case «0».re => linear_combination ((128)*x.re + (2048)*x.imJ)*h3
  case «0».imI => linear_combination ((-1280)*x.re + (-1237)*x.imI + (310)*x.imJ + (-2688)*x.imK)*h3
  case «0».imJ => linear_combination ((1024)*x.re + (128)*x.imJ)*h3
  case «0».imK => linear_combination ((768)*x.re + (-1344)*x.imI + (-655)*x.imJ + (-1237)*x.imK)*h3
  case «1».re => linear_combination ((-125)*x.re + (450)*x.imJ)*h3
  case «1».imI => linear_combination ((-375)*x.re + (-425)*x.imI + (232)*x.imJ + (-730)*x.imK)*h3
  case «1».imJ => linear_combination ((225)*x.re + (-124)*x.imJ)*h3
  case «1».imK => linear_combination ((225)*x.re + (-365)*x.imI + (-307)*x.imJ + (-424)*x.imK)*h3
  case «2».re => linear_combination ((1)*x.re + (2)*x.imJ)*h3
  case «2».imI => simp only [h3,or_true]
  case «2».imJ => linear_combination ((1)*x.re + (1)*x.imJ)*h3
  case «2».imK => simp only [h3,or_true]
  case «3».re => linear_combination ((315)*x.re + (882)*x.imJ)*h3
  case «3».imI => linear_combination ((-756)*x.re + (-272)*x.imI + (-154)*x.imJ + (-854)*x.imK)*h3
  case «3».imJ => linear_combination ((441)*x.re + (315)*x.imJ)*h3
  case «3».imK => linear_combination ((441)*x.re + (-427)*x.imI + (-142)*x.imJ + (-272)*x.imK)*h3

/-- The two composition orders differ by the explicitly constructed
original commutator unit. This is outer-action data, not a claimed commuting
four-generator action on the finite group. -/
theorem commutator_inner (i j : Fin 4) (x : Reduction) :
    reductionEquiv i (reductionEquiv j x)=
      reduction (commutatorUnit i j:PELPrincipalOrderCoordinates318.order)*
        reductionEquiv j (reductionEquiv i x)*
          reduction (((commutatorUnit i j)⁻¹:PELPrincipalOrderCoordinates318.orderˣ):PELPrincipalOrderCoordinates318.order) := by
  have h3 : (3:F3)=0 := by decide
  change forward i (forward j x)=
    reduction (PELPrincipalOrderCoordinates318.coordinatesEquiv (commutatorCoefficients i j))*
      forward j (forward i x)*
        reduction (PELPrincipalOrderCoordinates318.coordinatesEquiv (commutatorCoefficients j i))
  rw [reduction_coordinates,reduction_coordinates]
  fin_cases i <;> fin_cases j <;> ext <;>
    norm_num [forward,reduceCoordinates,commutatorCoefficients] <;> ring
  case «0».«1».re => linear_combination ((66619)*x.re + (188356)*x.imJ)*h3
  case «0».«1».imI => linear_combination ((62496)*x.re + (-19096)*x.imI + (156575)*x.imJ + (3834)*x.imK)*h3
  case «0».«1».imJ => linear_combination ((47089)*x.re + (133238)*x.imJ)*h3
  case «0».«1».imK => linear_combination ((-35805)*x.re + (15334)*x.imI + (-84803)*x.imJ + (-2387)*x.imK)*h3
  case «0».«2».re => linear_combination ((595)*x.re + (882)*x.imJ)*h3
  case «0».«2».imI => linear_combination ((945)*x.re + (27)*x.imI + (1869)*x.imJ + (266)*x.imK)*h3
  case «0».«2».imJ => linear_combination ((441)*x.re + (595)*x.imJ)*h3
  case «0».«2».imK => linear_combination ((-546)*x.re + (532)*x.imI + (-740)*x.imJ + (8)*x.imK)*h3
  case «0».«3».re => linear_combination ((658219)*x.re + (1028178)*x.imJ)*h3
  case «0».«3».imI => linear_combination ((1195956)*x.re + (1753304)*x.imI + (3883383)*x.imJ + (-54466)*x.imK)*h3
  case «0».«3».imJ => linear_combination ((514089)*x.re + (658219)*x.imJ)*h3
  case «0».«3».imK => linear_combination ((-691905)*x.re + (-108932)*x.imI + (-1102999)*x.imJ + (438326)*x.imK)*h3
  case «1».«0».re => linear_combination ((66619)*x.re + (188356)*x.imJ)*h3
  case «1».«0».imI => linear_combination ((62496)*x.re + (9548)*x.imI + (214061)*x.imJ + (7667)*x.imK)*h3
  case «1».«0».imJ => linear_combination ((47089)*x.re + (133238)*x.imJ)*h3
  case «1».«0».imK => linear_combination ((-35805)*x.re + (7668)*x.imI + (-71654)*x.imJ + (4774)*x.imK)*h3
  case «1».«2».re => linear_combination ((266)*x.re + (784)*x.imJ)*h3
  case «1».«2».imI => linear_combination ((364)*x.re + (112)*x.imI + (1444)*x.imJ + (18)*x.imK)*h3
  case «1».«2».imJ => linear_combination ((196)*x.re + (532)*x.imJ)*h3
  case «1».«2».imK => linear_combination ((-210)*x.re + (5)*x.imI + (-647)*x.imJ + (224)*x.imK)*h3
  case «1».«3».re => linear_combination ((147134)*x.re + (467856)*x.imJ)*h3
  case «1».«3».imI => linear_combination ((242478)*x.re + (-17636)*x.imI + (1515058)*x.imJ + (430464)*x.imK)*h3
  case «1».«3».imJ => linear_combination ((116964)*x.re + (294268)*x.imJ)*h3
  case «1».«3».imK => linear_combination ((-140220)*x.re + (107616)*x.imI + (-434695)*x.imJ + (-35272)*x.imK)*h3
  case «2».«0».re => linear_combination ((595)*x.re + (882)*x.imJ)*h3
  case «2».«0».imI => linear_combination ((945)*x.re + (8)*x.imI + (672)*x.imJ + (-1064)*x.imK)*h3
  case «2».«0».imJ => linear_combination ((441)*x.re + (595)*x.imJ)*h3
  case «2».«0».imK => linear_combination ((-546)*x.re + (-133)*x.imI + (-569)*x.imJ + (27)*x.imK)*h3
  case «2».«1».re => linear_combination ((266)*x.re + (784)*x.imJ)*h3
  case «2».«1».imI => linear_combination ((364)*x.re + (-224)*x.imI + (628)*x.imJ + (10)*x.imK)*h3
  case «2».«1».imJ => linear_combination ((196)*x.re + (532)*x.imJ)*h3
  case «2».«1».imK => linear_combination ((-210)*x.re + (9)*x.imI + (-459)*x.imJ + (-112)*x.imK)*h3
  case «2».«3».re => linear_combination ((50)*x.re + (72)*x.imJ)*h3
  case «2».«3».imI => linear_combination ((300)*x.re + (-32)*x.imI + (292)*x.imJ + (8)*x.imK)*h3
  case «2».«3».imJ => linear_combination ((36)*x.re + (50)*x.imJ)*h3
  case «2».«3».imK => linear_combination ((-174)*x.re + (4)*x.imI + (-162)*x.imJ + (-32)*x.imK)*h3
  case «3».«0».re => linear_combination ((658219)*x.re + (1028178)*x.imJ)*h3
  case «3».«0».imI => linear_combination ((1195956)*x.re + (-1753304)*x.imI + (484646)*x.imJ + (-54466)*x.imK)*h3
  case «3».«0».imJ => linear_combination ((514089)*x.re + (658219)*x.imJ)*h3
  case «3».«0».imK => linear_combination ((-691905)*x.re + (-108932)*x.imI + (-1097409)*x.imJ + (-438326)*x.imK)*h3
  case «3».«1».re => linear_combination ((147134)*x.re + (467856)*x.imJ)*h3
  case «3».«1».imI => linear_combination ((242478)*x.re + (-17636)*x.imI + (-167134)*x.imJ + (-430464)*x.imK)*h3
  case «3».«1».imJ => linear_combination ((116964)*x.re + (294268)*x.imJ)*h3
  case «3».«1».imK => linear_combination ((-140220)*x.re + (-107616)*x.imI + (-302527)*x.imJ + (-35272)*x.imK)*h3
  case «3».«2».re => linear_combination ((50)*x.re + (72)*x.imJ)*h3
  case «3».«2».imI => linear_combination ((300)*x.re + (32)*x.imI + (484)*x.imJ + (8)*x.imK)*h3
  case «3».«2».imJ => linear_combination ((36)*x.re + (50)*x.imJ)*h3
  case «3».«2».imK => linear_combination ((-174)*x.re + (4)*x.imI + (-266)*x.imJ + (32)*x.imK)*h3
end PELNormalizerInnerRelations318
