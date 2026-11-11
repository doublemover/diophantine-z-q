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
  left_inv x := by fin_cases i <;> ext <;> simp [forward,backward] <;> ring
  right_inv x := by fin_cases i <;> ext <;> simp [forward,backward] <;> ring
  map_add' x y := by fin_cases i <;> ext <;> simp [forward] <;> ring
  map_mul' x y := by fin_cases i <;> ext <;> simp [forward] <;> norm_num <;> ring

/-- The whole original reduction square commutes on EVERY integral element,
not only on a basis or on the semisimple residue field. -/
theorem original_conjugation (i : Fin 4) (x : order) :
    reduction (PELPrimeOrderConjugation318.orderEquiv i x)=reductionEquiv i (reduction x) := by
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  change reduction (coordinatesEquiv (PELPrimeOrderConjugation318.forward i
    (coordinatesEquiv.symm (coordinatesEquiv a))))=reductionEquiv i (reduction (coordinatesEquiv a))
  rw [AddEquiv.symm_apply_apply,reduction_coordinates,reduction_coordinates]
  fin_cases i <;> ext <;>
    norm_num [reductionEquiv,forward,reduceCoordinates,PELPrimeOrderConjugation318.forward] <;>
    push_cast <;> norm_num <;> ring

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
