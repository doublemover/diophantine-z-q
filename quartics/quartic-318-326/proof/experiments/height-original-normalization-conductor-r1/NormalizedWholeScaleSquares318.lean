module
public import NormalizedWholeScaleEquiv318
public import IntegralRootPointMaps318
public section
noncomputable section
namespace NormalizedWholeScaleSquares318
open Polynomial NormalizedWholeOverlap318 NormalizedReciprocalLaurent318 NormalizedWholeOpenMaps318
open NormalizedWholeScalarMaps318 NormalizedWholeScaleEquiv318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c d a : Fin 4 → R)
  (s : Fin 4 → Rˣ) (h : ∀ i,c i=d i*(s i:R)^2)

/-- The whole finite overlap square commutes on the entire polynomial base
and on all four specified signed generators. -/
theorem finite_square :
    (commonEquiv R c d a s h).toRingHom.comp (finiteMap R c a)=
      (finiteMap R d a).comp (finiteEquiv R c d a s h).toRingHom := by
  apply IntegralRootPointMaps318.four_ringHom_ext
  · apply RingHom.ext
    intro p
    change commonEquiv R c d a s h (finiteMap R c a (algebraMap R[X] (FiniteOrder R c a) p))=
      finiteMap R d a (finiteEquiv R c d a s h (algebraMap R[X] (FiniteOrder R c a) p))
    rw [finite_polynomial,AlgEquiv.commutes,AlgEquiv.commutes,finite_polynomial]
  · intro i
    change commonEquiv R c d a s h
      (finiteMap R c a (FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient R c a) i))=
      finiteMap R d a (finiteEquiv R c d a s h
        (FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient R c a) i))
    rw [NormalizedWholeRootMaps318.finite_generator,common_generator,
      NormalizedWholeScaleEquiv318.finite_generator,map_mul,finite_polynomial,
      NormalizedWholeRootMaps318.finite_generator]
    rw [←IsScalarTower.algebraMap_apply R R[X] (Laurent R)]

/-- The reciprocal square uses the same four scale multipliers and the
actual t-inverse overlap factor. Commutativity is checked without discarding
any root or replacing its sign. -/
theorem infinity_square :
    (commonEquiv R c d a s h).toRingHom.comp (infinityMap R c a)=
      (infinityMap R d a).comp (infinityEquiv R c d a s h).toRingHom := by
  apply IntegralRootPointMaps318.four_ringHom_ext
  · apply RingHom.ext
    intro p
    change commonEquiv R c d a s h (infinityMap R c a (algebraMap R[X] (InfinityOrder R c a) p))=
      infinityMap R d a (infinityEquiv R c d a s h (algebraMap R[X] (InfinityOrder R c a) p))
    rw [infinity_polynomial,AlgEquiv.commutes,AlgEquiv.commutes,infinity_polynomial]
  · intro i
    change commonEquiv R c d a s h
      (infinityMap R c a (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient R c a) i))=
      infinityMap R d a (infinityEquiv R c d a s h
        (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient R c a) i))
    rw [NormalizedWholeRootMaps318.infinity_generator,Algebra.smul_def,map_mul,
      AlgEquiv.commutes,common_generator,NormalizedWholeScaleEquiv318.infinity_generator,
      map_mul,infinity_polynomial,NormalizedWholeRootMaps318.infinity_generator,Algebra.smul_def]
    simp only [reciprocalMap,Polynomial.aeval_C]
    ring
end NormalizedWholeScaleSquares318
