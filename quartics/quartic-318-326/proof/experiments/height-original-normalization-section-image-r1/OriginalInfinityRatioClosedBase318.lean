module
public import OriginalInfinityRatioParameters318
public section
noncomputable section
namespace OriginalInfinityRatioClosedBase318
open Polynomial OriginalInfinityRatioParameters318
variable (V : Type*) [CommRing V] (d a : Fin 4 → V) (h0 : IsUnit (d 0))

include h0 in
lemma denominator_zero_unit : IsUnit ((Polynomial.evalRingHom (0:V)) (denominator V d a)) := by
  simpa only [denominator,eval_mul,eval_sub,eval_one,eval_C,eval_X,mul_zero,sub_zero,mul_one] using h0

/-- The actual infinity base section is retained on this localization
when the chosen pivot coefficient is a unit. This premise is explicit. -/
@[expose] def atInfinity : Base V d a →+* V :=
  IsLocalization.Away.lift (g:=Polynomial.evalRingHom (0:V)) (denominator V d a)
    (denominator_zero_unit V d a h0)

lemma atInfinity_polynomial (p : V[X]) : atInfinity V d a h0 (algebraMap V[X] (Base V d a) p)=p.eval 0 :=
  IsLocalization.Away.lift_eq _ _ p
lemma coordinate_zero : atInfinity V d a h0 (coordinate V d a)=0 := by
  rw [coordinate,atInfinity_polynomial,eval_X]
lemma common_zero : atInfinity V d a h0 (common V d a)=0 := by
  rw [common,atInfinity_polynomial]
  simp only [DVRNormalizedInfinityOrder318.coefficient,eval_mul,eval_sub,eval_C,eval_X,
    eval_one,mul_zero,zero_mul]
lemma scalar_fixed (v : V) : atInfinity V d a h0
    (algebraMap V[X] (Base V d a) (C v))=v := by rw [atInfinity_polynomial,eval_C]

/-- Over the original characteristic-zero generic coefficient field,
every nonzero pivot automatically supplies this actual infinity lift. -/
@[expose] def genericInfinity {K : Type*} [Field K] (d a : Fin 4 → K) (h0 : d 0≠0) :
    Base K d a →+* K := atInfinity K d a (IsUnit.mk0 _ h0)
end OriginalInfinityRatioClosedBase318
