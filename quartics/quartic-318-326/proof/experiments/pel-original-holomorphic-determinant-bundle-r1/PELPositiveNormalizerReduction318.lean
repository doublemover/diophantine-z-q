module
public import PELEffectivePositiveLevel318
public import PELNormalizerPrincipalConjugation318
public section
noncomputable section
namespace PELPositiveNormalizerReduction318
open PELPrincipalOrderCoordinates318 PELOrderReductionThree318 PELQuaternionAlgebra318
open PELPositiveOrderNormalizer318 PELNormalizerPrincipalConjugation318
set_option maxHeartbeats 1400000

/-- Every actual integral ring equivalence preserves literal3O, in both
directions. The quotient action does not use a choice of residue lifts. -/
theorem moduloThree_equiv (e : order ≃+* order) :
    moduloThree=moduloThree.comap e := by
  ext x y
  change moduloThree x y ↔ moduloThree (e x) (e y)
  rw [moduloThree_iff,moduloThree_iff]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨e z,?_⟩
    have h := congrArg e hz
    simpa only [map_sub,map_zsmul] using h
  · rintro ⟨z,hz⟩
    refine ⟨e.symm z,?_⟩
    have h := congrArg e.symm hz
    simpa only [map_sub,map_zsmul,RingEquiv.symm_apply_apply] using h

/-- ANY positive original-order normalizer acts on the literal O/3O by
its actual whole-order conjugation, extending the earlier four tables. -/
@[expose] def quotientConjugation (g : positiveNormalizer) : QuotientOrder ≃+* QuotientOrder :=
  RingCon.congr (conjugation g) (moduloThree_equiv (conjugation g))

theorem quotientConjugation_mk (g : positiveNormalizer) (x : order) :
    quotientConjugation g (moduloThree.mk' x)=moduloThree.mk' (conjugation g x) := rfl

/-- The finite norm is the reduction of the SAME integer norm, so equality
of original rational norms implies equality of those finite norms. -/
theorem norm_reduction_eq (x y : order) (h : reducedNorm (x:B)=reducedNorm (y:B)) :
    PELLevelThreeSimilitudes318.norm (moduloThree.mk' x)=
      PELLevelThreeSimilitudes318.norm (moduloThree.mk' y) := by
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  obtain ⟨b,rfl⟩ := coordinatesEquiv.surjective y
  have hq : (PELLevelThreeSimilitudes318.integralNorm a:ℚ)=
      (PELLevelThreeSimilitudes318.integralNorm b:ℚ) := by
    rw [←PELLevelThreeSimilitudes318.original_norm,←PELLevelThreeSimilitudes318.original_norm]
    exact h
  have hz : PELLevelThreeSimilitudes318.integralNorm a=
      PELLevelThreeSimilitudes318.integralNorm b := by exact_mod_cast hq
  rw [PELLevelThreeSimilitudes318.norm_original,PELLevelThreeSimilitudes318.norm_original,hz]

theorem quotient_norm (g : positiveNormalizer) (x : QuotientOrder) :
    PELLevelThreeSimilitudes318.norm (quotientConjugation g x)=
      PELLevelThreeSimilitudes318.norm x := by
  obtain ⟨x,rfl⟩ := moduloThree.mk'_surjective x
  rw [quotientConjugation_mk]
  exact norm_reduction_eq _ _ (conjugation_norm g x)

theorem original_conjugation_mul (g h : positiveNormalizer) (x : order) :
    conjugation (g*h) x=conjugation g (conjugation h x) := by
  apply Subtype.ext
  change ((g.val:B)*(h.val:B))*(x:B)*((↑h.val⁻¹:B)*(↑g.val⁻¹:B))=
    (g.val:B)*((h.val:B)*(x:B)*(↑h.val⁻¹:B))*(↑g.val⁻¹:B)
  noncomm_ring

theorem quotientConjugation_one (x : QuotientOrder) : quotientConjugation 1 x=x := by
  obtain ⟨x,rfl⟩ := moduloThree.mk'_surjective x
  rw [quotientConjugation_mk]
  congr 1
  apply Subtype.ext
  change (1:B)*(x:B)*1=(x:B)
  simp

theorem quotientConjugation_mul (g h : positiveNormalizer) (x : QuotientOrder) :
    quotientConjugation (g*h) x=quotientConjugation g (quotientConjugation h x) := by
  obtain ⟨x,rfl⟩ := moduloThree.mk'_surjective x
  rw [quotientConjugation_mk,quotientConjugation_mk,quotientConjugation_mk,original_conjugation_mul]
end PELPositiveNormalizerReduction318
