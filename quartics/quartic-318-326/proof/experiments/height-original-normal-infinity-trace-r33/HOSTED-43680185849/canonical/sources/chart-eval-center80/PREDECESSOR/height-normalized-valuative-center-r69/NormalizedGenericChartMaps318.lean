module
public import NormalizedWholeRootMaps318
public section
noncomputable section
namespace NormalizedGenericChartMaps318
open Polynomial IntegralRootPointMaps318 NormalizedWholeOverlap318
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
  (d a : Fin 4 → R)

section Finite
variable (t : K) (z : Fin 4 → K)
  (hz : ∀ i,(z i)^2=algebraMap R K (d i)*(t-algebraMap R K (a i)))
local instance evaluationAlgebra : Algebra R[X] K := (Polynomial.aeval t).toRingHom.toAlgebra

include hz in
theorem finite_relation (i : Fin 4) : (z i)^2=
    algebraMap R[X] K (DVRNormalizedFiniteOrder318.coefficient R d a i) := by
  change (z i)^2=Polynomial.aeval t _
  simpa only [DVRNormalizedFiniteOrder318.coefficient,map_mul,map_sub,
    Polynomial.aeval_C,Polynomial.aeval_X] using hz i

@[expose] def finiteMap : FiniteOrder R d a →+* K :=
  (fourMap (DVRNormalizedFiniteOrder318.coefficient R d a) z
    (finite_relation R K d a t z hz)).toRingHom

theorem finite_polynomial (p : R[X]) :
    finiteMap R K d a t z hz (algebraMap R[X] (FiniteOrder R d a) p)=Polynomial.aeval t p :=
  (fourMap _ _ (finite_relation R K d a t z hz)).commutes p

theorem finite_generator (i : Fin 4) :
    finiteMap R K d a t z hz (FourRootOrderSigns318.generator
      (DVRNormalizedFiniteOrder318.coefficient R d a) i)=z i := fourMap_generator _ _ _ i
end Finite

section Infinity
variable (w : K) (v : Fin 4 → K)
  (hv : ∀ i,(v i)^2=algebraMap R K (d i)*w*(1-algebraMap R K (a i)*w))
local instance evaluationAlgebra : Algebra R[X] K := (Polynomial.aeval w).toRingHom.toAlgebra

include hv in
theorem infinity_relation (i : Fin 4) : (v i)^2=
    algebraMap R[X] K (DVRNormalizedInfinityOrder318.coefficient R d a i) := by
  change (v i)^2=Polynomial.aeval w _
  simpa only [DVRNormalizedInfinityOrder318.coefficient,map_mul,map_sub,map_one,
    Polynomial.aeval_C,Polynomial.aeval_X] using hv i

@[expose] def infinityMap : InfinityOrder R d a →+* K :=
  (fourMap (DVRNormalizedInfinityOrder318.coefficient R d a) v
    (infinity_relation R K d a w v hv)).toRingHom

theorem infinity_polynomial (p : R[X]) :
    infinityMap R K d a w v hv (algebraMap R[X] (InfinityOrder R d a) p)=Polynomial.aeval w p :=
  (fourMap _ _ (infinity_relation R K d a w v hv)).commutes p

theorem infinity_generator (i : Fin 4) :
    infinityMap R K d a w v hv (FourRootOrderSigns318.generator
      (DVRNormalizedInfinityOrder318.coefficient R d a) i)=v i := fourMap_generator _ _ _ i
end Infinity

/-- The reciprocal root is the same signed root divided by the original
coordinate; neither the contact difference nor the twist is assumed a unit. -/
theorem reciprocal_roots (t : K) (ht : t≠0) (z : Fin 4 → K)
    (hz : ∀ i,(z i)^2=algebraMap R K (d i)*(t-algebraMap R K (a i))) (i : Fin 4) :
    (z i/t)^2=algebraMap R K (d i)*t⁻¹*(1-algebraMap R K (a i)*t⁻¹) := by
  rw [div_pow,hz]
  field_simp [ht]
  <;> ring
end NormalizedGenericChartMaps318
