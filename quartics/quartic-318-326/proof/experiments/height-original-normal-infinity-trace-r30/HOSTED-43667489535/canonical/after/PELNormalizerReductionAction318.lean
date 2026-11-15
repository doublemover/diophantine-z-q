module
public import PELPrimeLatticeCokernel318
public section
noncomputable section
namespace PELNormalizerReductionAction318
open PELOrderReductionThree318 PELPrincipalOrderCoordinates318
set_option maxHeartbeats 1600000

/-- Literal reduction of the four ORIGINAL integral conjugation matrices.
The norm3 case remains a ring automorphism, unlike multiplication by n3. -/
@[expose] def forward (i : Fin 4) (x : Reduction) : Reduction :=
  ![⟨x.re,x.imJ+x.imK,x.imJ,2*x.imI+x.imJ⟩,
    ⟨x.re,x.imI+2*x.imJ,2*x.imJ,x.imJ+2*x.imK⟩,
    ⟨x.re,2*x.imK,x.imJ,x.imI⟩,
    ⟨x.re,2*x.imI,x.imJ,2*x.imJ+2*x.imK⟩] i
@[expose] def backward (i : Fin 4) (x : Reduction) : Reduction :=
  ![⟨x.re,x.imJ+2*x.imK,x.imJ,x.imI+2*x.imJ⟩,
    ⟨x.re,x.imI+2*x.imJ,2*x.imJ,2*x.imJ+2*x.imK⟩,
    ⟨x.re,x.imK,x.imJ,2*x.imI⟩,
    ⟨x.re,2*x.imI,x.imJ,2*x.imJ+2*x.imK⟩] i

@[expose] def reductionEquiv (i : Fin 4) : Reduction ≃+* Reduction where
  toFun := forward i
  invFun := backward i
  left_inv x := by
    have h3 : (3:F3)=0 := by decide
    fin_cases i <;> ext <;> simp [forward,backward] <;> ring
    case «0».imI => linear_combination (x.imI + x.imJ)*h3
    case «0».imK => linear_combination (x.imJ)*h3
    case «1».imI => linear_combination (2*x.imJ)*h3
    case «1».imJ => linear_combination (x.imJ)*h3
    case «1».imK => linear_combination (2*x.imJ + x.imK)*h3
    case «2».imK => linear_combination (x.imK)*h3
    case «3».imI => linear_combination (x.imI)*h3
    case «3».imK => linear_combination (2*x.imJ + x.imK)*h3
  right_inv x := by
    have h3 : (3:F3)=0 := by decide
    fin_cases i <;> ext <;> simp [forward,backward] <;> ring
    case «0».imI => linear_combination (x.imJ)*h3
    case «0».imK => linear_combination (x.imJ + x.imK)*h3
    case «1».imI => linear_combination (2*x.imJ)*h3
    case «1».imJ => linear_combination (x.imJ)*h3
    case «1».imK => linear_combination (2*x.imJ + x.imK)*h3
    case «2».imI => linear_combination (x.imI)*h3
    case «3».imI => linear_combination (x.imI)*h3
    case «3».imK => linear_combination (2*x.imJ + x.imK)*h3
  map_add' x y := by fin_cases i <;> ext <;> simp [forward] <;> ring
  map_mul' x y := by
    have h3 : (3:F3)=0 := by decide
    fin_cases i <;> ext <;> simp [forward] <;> norm_num <;> ring
    case «0».imI => linear_combination (-x.imI*y.imJ + x.imJ*y.imI)*h3
    case «0».imK => linear_combination (-x.imJ*y.imK + x.imK*y.imJ)*h3
    case «1».re => linear_combination (-2*x.imJ*y.imJ)*h3
    case «1».imI => linear_combination (2*x.imJ*y.imK - 2*x.imK*y.imJ)*h3

/-- The whole original reduction square commutes on EVERY integral element,
not only on a basis or on the semisimple residue field. -/
theorem original_conjugation (i : Fin 4) (x : order) :
    reduction (PELPrimeOrderConjugation318.orderEquiv i x)=reductionEquiv i (reduction x) := by
  have h3 : (3:F3)=0 := by decide
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  change reduction (coordinatesEquiv (PELPrimeOrderConjugation318.forward i
    (coordinatesEquiv.symm (coordinatesEquiv a))))=reductionEquiv i (reduction (coordinatesEquiv a))
  rw [AddEquiv.symm_apply_apply,reduction_coordinates,reduction_coordinates]
  fin_cases i <;> ext <;>
    norm_num [reductionEquiv,forward,reduceCoordinates,PELPrimeOrderConjugation318.forward] <;>
    push_cast <;> norm_num <;> ring
  case «0».re => linear_combination (294*(a 1:F3) - 21*(a 2:F3) + 168*(a 3:F3))*h3
  case «0».imI => linear_combination (276*(a 1:F3) - 20*(a 2:F3) + 156*(a 3:F3))*h3
  case «0».imJ => linear_combination (196*(a 1:F3) - 14*(a 2:F3) + 112*(a 3:F3))*h3
  case «0».imK => linear_combination (-159*(a 1:F3) + 12*(a 2:F3) - 89*(a 3:F3))*h3
  case «1».re => linear_combination (210*(a 1:F3) - 14*(a 2:F3) + 126*(a 3:F3))*h3
  case «1».imI => linear_combination (166*(a 1:F3) - 11*(a 2:F3) + 99*(a 3:F3))*h3
  case «1».imJ => linear_combination (140*(a 1:F3) - 9*(a 2:F3) + 84*(a 3:F3))*h3
  case «1».imK => linear_combination (-95*(a 1:F3) + 7*(a 2:F3) - 57*(a 3:F3))*h3
  case «2».imI => linear_combination (3*(a 1:F3))*h3
  case «2».imK => linear_combination (-2*(a 1:F3))*h3
  case «3».re => linear_combination (126*(a 1:F3) - 6*(a 2:F3) + 84*(a 3:F3))*h3
  case «3».imI => linear_combination (422*(a 1:F3) - 23*(a 2:F3) + 279*(a 3:F3))*h3
  case «3».imJ => linear_combination (84*(a 1:F3) - 4*(a 2:F3) + 56*(a 3:F3))*h3
  case «3».imK => linear_combination (-245*(a 1:F3) + 14*(a 2:F3) - 162*(a 3:F3))*h3

/-- Actual ring automorphism of the literal original quotient O/3O. -/
@[expose] def quotientConjugation (i : Fin 4) : QuotientOrder ≃+* QuotientOrder :=
  quotientEquiv.trans ((reductionEquiv i).trans quotientEquiv.symm)

theorem quotientConjugation_mk (i : Fin 4) (x : order) :
    quotientConjugation i (moduloThree.mk' x)=
      moduloThree.mk' (PELPrimeOrderConjugation318.orderEquiv i x) := by
  change quotientEquiv.symm (reductionEquiv i (quotientEquiv (moduloThree.mk' x)))=_
  apply quotientEquiv.injective
  rw [RingEquiv.apply_symm_apply,quotientEquiv_mk,quotientEquiv_mk]
  exact (original_conjugation i x).symm
end PELNormalizerReductionAction318
