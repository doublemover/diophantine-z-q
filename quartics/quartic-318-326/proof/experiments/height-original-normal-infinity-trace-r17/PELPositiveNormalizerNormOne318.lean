module
public import PELPositiveNormalizerReduction318
public section
noncomputable section
namespace PELPositiveNormalizerNormOne318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerReduction318 PELOrderReductionThree318
open PELFiniteNormOneGroup318 PELGlobalUnitReductionSurjective318
open PELNormalizerPrincipalConjugation318
set_option maxHeartbeats 1400000

@[expose] def unitConjugation (g : positiveNormalizer) : QuotientOrderˣ ≃* QuotientOrderˣ :=
  Units.mapEquiv (quotientConjugation g).toMulEquiv

theorem original_reduction (g : positiveNormalizer) (u : PELPrincipalOrderCoordinates318.orderˣ) :
    unitConjugation g (originalUnitReduction u)=originalUnitReduction (conjugateUnit g u) := by
  apply Units.ext
  exact quotientConjugation_mk g (u:PELPrincipalOrderCoordinates318.order)

@[expose] def normOneConjugation (g : positiveNormalizer) : normOne ≃* normOne where
  toFun u := ⟨unitConjugation g u.val,(mem_normOne _).mpr
    ((quotient_norm g (u.val:QuotientOrder)).trans ((mem_normOne _).mp u.property))⟩
  invFun u := ⟨(unitConjugation g).symm u.val,by
    apply (mem_normOne _).mpr
    have h := quotient_norm g ((unitConjugation g).symm u.val:QuotientOrder)
    change PELLevelThreeSimilitudes318.norm
      (unitConjugation g ((unitConjugation g).symm u.val):QuotientOrder)=_ at h
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm.trans ((mem_normOne _).mp u.property)⟩
  left_inv u := Subtype.ext ((unitConjugation g).symm_apply_apply u.val)
  right_inv u := Subtype.ext ((unitConjugation g).apply_symm_apply u.val)
  map_mul' u v := Subtype.ext ((unitConjugation g).map_mul u.val v.val)

theorem normOneConjugation_minusOne (g : positiveNormalizer) :
    normOneConjugation g PELEffectivePositiveLevel318.minusOne=PELEffectivePositiveLevel318.minusOne := by
  apply Subtype.ext
  apply Units.ext
  change quotientConjugation g (-1:QuotientOrder)= -1
  simp

/-- Full original global norm-one conjugation, not just a finite action
specified by four residue matrices. -/
@[expose] def globalConjugation (g : positiveNormalizer) :
    PELJointNormOneAction318.normOneUnits →* PELJointNormOneAction318.normOneUnits where
  toFun u := ⟨conjugateUnit g u.val,by
    apply (PELJointNormOneAction318.mem_normOneUnits _).mpr
    change PELQuaternionAlgebra318.reducedNorm (conjugation g (u.val:PELPrincipalOrderCoordinates318.order):PELQuaternionAlgebra318.B)=1
    rw [conjugation_norm]
    exact (PELJointNormOneAction318.mem_normOneUnits _).mp u.property⟩
  map_one' := Subtype.ext (map_one (conjugateUnit g))
  map_mul' u v := Subtype.ext (map_mul (conjugateUnit g) u.val v.val)

theorem normOne_reduction_square (g : positiveNormalizer) (u : PELJointNormOneAction318.normOneUnits) :
    normOneConjugation g (PELActualPrincipalThreeQuotient318.normOneReduction u)=
      PELActualPrincipalThreeQuotient318.normOneReduction (globalConjugation g u) :=
  Subtype.ext (original_reduction g u.val)

theorem normOneConjugation_one (u : normOne) : normOneConjugation 1 u=u := by
  apply Subtype.ext
  apply Units.ext
  exact quotientConjugation_one (u.val:QuotientOrder)

theorem normOneConjugation_mul (g h : positiveNormalizer) (u : normOne) :
    normOneConjugation (g*h) u=normOneConjugation g (normOneConjugation h u) := by
  apply Subtype.ext
  apply Units.ext
  exact quotientConjugation_mul g h (u.val:QuotientOrder)
end PELPositiveNormalizerNormOne318
