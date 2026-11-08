module
public import InfinitySignPoint318
public section
noncomputable section
namespace InfinityBasePoint318
open Polynomial AlgebraicGeometry CategoryTheory InfinityReciprocalAction318
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
lemma denominator_at_zero_ne_zero:
    Polynomial.eval 0 (ReciprocalInfinityBase318.reciprocalDenominator c)≠0:=by
  rw [ReciprocalInfinityBase318.reciprocalDenominator_at_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun j _=>div_ne_zero (c j.succ).ne_zero (c 0).ne_zero)
@[expose] def rationalPoint:Base c→+*ℚ:=
  IsLocalization.Away.lift (g:=Polynomial.evalRingHom 0)
    (ReciprocalInfinityBase318.reciprocalDenominator c)
    (IsUnit.mk0 _ (denominator_at_zero_ne_zero c))
lemma on_polynomial (f:ℚ[X]):rationalPoint c (algebraMap ℚ[X] (Base c) f)=Polynomial.eval 0 f:=
  IsLocalization.Away.lift_eq _ _ _
variable {F:Type} [Field F] [Algebra ℚ F]
@[expose] def fieldPoint:Base c→+*F:=(algebraMap ℚ F).comp (rationalPoint c)
lemma fieldPoint_coordinate:fieldPoint (F:=F) c (algebraMap ℚ[X] (Base c) X)=0:=by
  change algebraMap ℚ F (rationalPoint c (algebraMap ℚ[X] (Base c) X))=0
  rw [on_polynomial,Polynomial.eval_X,map_zero]
/-- The literal infinity point in the actual reciprocal projective chart. -/
@[expose] def infinityPoint:Spec (CommRingCat.of F)⟶ProjectiveJLine318.scheme ℚ:=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (0:F)).toRingHom)≫JLineAtlas318.chart ℚ 0
/-- The actual localized reciprocal base contains precisely this point. -/
theorem fieldPoint_over_infinity:
    Spec.map (CommRingCat.ofHom (fieldPoint (F:=F) c))≫InfinityGlobalBase318.baseOpen c=
      infinityPoint (F:=F):=by
  unfold InfinityGlobalBase318.baseOpen infinityPoint
  rw [←Category.assoc,←Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro q
    change algebraMap ℚ F (rationalPoint c (algebraMap ℚ[X] (Base c) (C q)))=_
    rw [on_polynomial,Polynomial.eval_C]
    exact (Polynomial.aeval_C _ _).symm
  · exact (fieldPoint_coordinate c).trans (Polynomial.aeval_X _).symm
end InfinityBasePoint318
