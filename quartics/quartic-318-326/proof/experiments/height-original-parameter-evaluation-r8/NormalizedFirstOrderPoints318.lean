module
public import FourRootFirstOrderPoint318
public import DVRNormalizedInfinityOrder318
public section
noncomputable section
namespace NormalizedFirstOrderPoints318
open Polynomial FourRootFirstOrderPoint318
variable (V K : Type*) [CommRing V] [Field K] [CharZero K] [Algebra V K]
  (d a : Fin 4 → V) (t : K) (z : Fin 4 → K) (hz0 : ∀ i,z i≠0)

/-- The literal first-order relation for d_i (T-a_i). No d_i is inverted in
V and no integral unit-2 assumption is used; derivative values lie in K. -/
theorem finite_relation
    (hz : ∀ i,(z i)^2=algebraMap V K (d i)*(t-algebraMap V K (a i))) (i : Fin 4) :
    rootJet K (z i) (algebraMap V K (d i)) ^ 2=
      Polynomial.aeval (parameter K t) (DVRNormalizedFiniteOrder318.coefficient V d a i) := by
  rw [rootJet_square K _ _ (hz0 i)]
  simp only [DVRNormalizedFiniteOrder318.coefficient,map_mul,map_sub,
    Polynomial.aeval_C,Polynomial.aeval_X]
  apply TrivSqZeroExt.ext
  · change (z i)^2=algebraMap V K (d i)*(t-algebraMap V K (a i))
    exact hz i
  · change algebraMap V K (d i)=algebraMap V K (d i)*(1-0)+0*(t-algebraMap V K (a i))
    ring

@[expose] def finiteLift
    (hz : ∀ i,(z i)^2=algebraMap V K (d i)*(t-algebraMap V K (a i))) :
    DVRNormalizedFiniteOrder318.Order V d a →ₐ[V] TrivSqZeroExt K K :=
  FourRootFirstOrderPoint318.lift V K (DVRNormalizedFiniteOrder318.coefficient V d a) t
    (fun i => rootJet K (z i) (algebraMap V K (d i))) (finite_relation V K d a t z hz0 hz)

/-- The literal reciprocal derivative is d_i*(1-2*a_i*w). This parameter is
w itself; translating to the original Dt still requires dw=-t^-2 dt. -/
theorem infinity_relation
    (hz : ∀ i,(z i)^2=algebraMap V K (d i)*t*(1-algebraMap V K (a i)*t)) (i : Fin 4) :
    rootJet K (z i) (algebraMap V K (d i)*(1-2*algebraMap V K (a i)*t)) ^ 2=
      Polynomial.aeval (parameter K t) (DVRNormalizedInfinityOrder318.coefficient V d a i) := by
  rw [rootJet_square K _ _ (hz0 i)]
  simp only [DVRNormalizedInfinityOrder318.coefficient,map_mul,map_sub,map_one,
    Polynomial.aeval_C,Polynomial.aeval_X]
  apply TrivSqZeroExt.ext
  · change (z i)^2=algebraMap V K (d i)*t*(1-algebraMap V K (a i)*t)
    exact hz i
  · change algebraMap V K (d i)*(1-2*algebraMap V K (a i)*t)=
      (algebraMap V K (d i)*t)*(0-(algebraMap V K (a i)*1+0*t))+
        (algebraMap V K (d i)*1+0*t)*(1-algebraMap V K (a i)*t)
    ring

@[expose] def infinityLift
    (hz : ∀ i,(z i)^2=algebraMap V K (d i)*t*(1-algebraMap V K (a i)*t)) :
    DVRNormalizedInfinityOrder318.Order V d a →ₐ[V] TrivSqZeroExt K K :=
  FourRootFirstOrderPoint318.lift V K (DVRNormalizedInfinityOrder318.coefficient V d a) t
    (fun i => rootJet K (z i) (algebraMap V K (d i)*(1-2*algebraMap V K (a i)*t)))
    (infinity_relation V K d a t z hz0 hz)
end NormalizedFirstOrderPoints318
