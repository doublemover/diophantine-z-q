module
public import PELPositiveNormalizerNormOne318
public section
noncomputable section
namespace PELPositiveNormalizerEffective318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerNormOne318 PELEffectivePositiveLevel318
set_option maxHeartbeats 1200000

theorem signs_preserved (g : positiveNormalizer) :
    signs.map (normOneConjugation g).toMonoidHom=signs := by
  rw [signs,MonoidHom.map_zpowers,normOneConjugation_minusOne]

/-- Actual automorphism of the18-element effective positive-level group
for EVERY positive original-order normalizer. -/
@[expose] def effectiveConjugation (g : positiveNormalizer) :
    EffectivePositiveLevel ≃* EffectivePositiveLevel :=
  QuotientGroup.congr _ _ (normOneConjugation g) (signs_preserved g)

theorem effectiveConjugation_mk (g : positiveNormalizer) (u : PELFiniteNormOneGroup318.normOne) :
    effectiveConjugation g (QuotientGroup.mk u)=QuotientGroup.mk (normOneConjugation g u) := rfl

/-- This is the exact original reduction square needed to transport the
analytic18-point fiber labels. No unlabeled permutation is substituted. -/
theorem effective_reduction_square (g : positiveNormalizer) (u : PELJointNormOneAction318.normOneUnits) :
    effectiveConjugation g (effectiveReduction u)=effectiveReduction (globalConjugation g u) := by
  change effectiveConjugation g (QuotientGroup.mk (PELActualPrincipalThreeQuotient318.normOneReduction u))=_
  rw [effectiveConjugation_mk,normOne_reduction_square] <;> rfl

/-- The actual effective kernel is preserved as a consequence of that
whole reduction square, retaining both original ±1 congruence classes. -/
theorem effective_kernel_preserved (g : positiveNormalizer) (u : PELJointNormOneAction318.normOneUnits)
    (hu : u∈effectiveReduction.ker) : globalConjugation g u∈effectiveReduction.ker := by
  change effectiveReduction (globalConjugation g u)=1
  rw [←effective_reduction_square]
  change effectiveConjugation g (effectiveReduction u)=1
  rw [show effectiveReduction u=1 from hu,map_one]

theorem effectiveConjugation_one (x : EffectivePositiveLevel) : effectiveConjugation 1 x=x := by
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective signs x
  rw [effectiveConjugation_mk,normOneConjugation_one]

theorem effectiveConjugation_mul (g h : positiveNormalizer) (x : EffectivePositiveLevel) :
    effectiveConjugation (g*h) x=effectiveConjugation g (effectiveConjugation h x) := by
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective signs x
  rw [effectiveConjugation_mk,effectiveConjugation_mk,effectiveConjugation_mk,normOneConjugation_mul]

/-- A genuine action homomorphism, with original normalizer composition,
not an independently chosen collection of finite permutations. -/
@[expose] def effectiveAction : positiveNormalizer →* MulAut EffectivePositiveLevel where
  toFun := effectiveConjugation
  map_one' := by ext x; exact effectiveConjugation_one x
  map_mul' g h := by ext x; exact effectiveConjugation_mul g h x
end PELPositiveNormalizerEffective318
