module
public import NormalizedWholeRootMaps318
public import FourRootIndividualScales318
public section
noncomputable section
namespace NormalizedWholeScaleEquiv318
open Polynomial NormalizedWholeOverlap318 NormalizedReciprocalLaurent318 NormalizedWholeOpenMaps318
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c d a : Fin 4 → R)
  (s : Fin 4 → Rˣ) (h : ∀ i,c i=d i*(s i:R)^2)
@[expose] def polynomialUnit (i : Fin 4) : R[X]ˣ := Units.map C.toMonoidHom (s i)
@[expose] def laurentUnit (i : Fin 4) : (Laurent R)ˣ :=
  Units.map (algebraMap R (Laurent R)).toMonoidHom (s i)

include h in
theorem finite_relation (i : Fin 4) :
    DVRNormalizedFiniteOrder318.coefficient R c a i=
      DVRNormalizedFiniteOrder318.coefficient R d a i*(polynomialUnit R s i:R[X])^2 := by
  change C (c i)*(X-C (a i))=(C (d i)*(X-C (a i)))*(C (s i:R))^2
  rw [h i,map_mul,map_pow]
  ring

include h in
theorem infinity_relation (i : Fin 4) :
    DVRNormalizedInfinityOrder318.coefficient R c a i=
      DVRNormalizedInfinityOrder318.coefficient R d a i*(polynomialUnit R s i:R[X])^2 := by
  change C (c i)*X*(1-C (a i)*X)=(C (d i)*X*(1-C (a i)*X))*(C (s i:R))^2
  rw [h i,map_mul,map_pow]
  ring

include h in
theorem common_relation (i : Fin 4) :
    finiteParameter R c a i=finiteParameter R d a i*(laurentUnit R s i:Laurent R)^2 := by
  rw [finiteParameter,finite_relation R c d a s h,map_mul,map_pow]
  change finiteParameter R d a i * (algebraMap R[X] (Laurent R) (C (s i:R)))^2=_
  rw [←IsScalarTower.algebraMap_apply R R[X] (Laurent R)]
  all_goals rfl

@[expose] def finiteEquiv : FiniteOrder R c a ≃ₐ[R[X]] FiniteOrder R d a :=
  FourRootIndividualScales318.four _ _ (polynomialUnit R s) (finite_relation R c d a s h)
@[expose] def infinityEquiv : InfinityOrder R c a ≃ₐ[R[X]] InfinityOrder R d a :=
  FourRootIndividualScales318.four _ _ (polynomialUnit R s) (infinity_relation R c d a s h)
@[expose] def commonEquiv : CommonOrder R c a ≃ₐ[Laurent R] CommonOrder R d a :=
  FourRootIndividualScales318.four _ _ (laurentUnit R s) (common_relation R c d a s h)

theorem finite_generator (i : Fin 4) :
    finiteEquiv R c d a s h (FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient R c a) i)=
      algebraMap R[X] (FiniteOrder R d a) (C (s i:R))*
        FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient R d a) i := by
  simpa only [Algebra.smul_def] using FourRootIndividualScales318.four_generator
    (DVRNormalizedFiniteOrder318.coefficient R d a) (DVRNormalizedFiniteOrder318.coefficient R c a)
    (polynomialUnit R s) (finite_relation R c d a s h) i

theorem infinity_generator (i : Fin 4) :
    infinityEquiv R c d a s h (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient R c a) i)=
      algebraMap R[X] (InfinityOrder R d a) (C (s i:R))*
        FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient R d a) i := by
  simpa only [Algebra.smul_def] using FourRootIndividualScales318.four_generator
    (DVRNormalizedInfinityOrder318.coefficient R d a) (DVRNormalizedInfinityOrder318.coefficient R c a)
    (polynomialUnit R s) (infinity_relation R c d a s h) i

theorem common_generator (i : Fin 4) :
    commonEquiv R c d a s h (FourRootOrderSigns318.generator (finiteParameter R c a) i)=
      algebraMap (Laurent R) (CommonOrder R d a) (algebraMap R (Laurent R) (s i:R))*
        FourRootOrderSigns318.generator (finiteParameter R d a) i := by
  simpa only [Algebra.smul_def] using FourRootIndividualScales318.four_generator
    (finiteParameter R d a) (finiteParameter R c a) (laurentUnit R s) (common_relation R c d a s h) i
end NormalizedWholeScaleEquiv318
