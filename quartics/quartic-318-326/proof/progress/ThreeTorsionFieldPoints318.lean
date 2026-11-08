module
public import ThreeTorsionFunctor318
public import ThreeTorsionPoints318
public section
noncomputable section
namespace ThreeTorsionFieldPoints318
open Polynomial ThreeTorsionAlgebra318
set_option maxHeartbeats 0
variable {R K:Type*} [CommRing R] [Field K] [DecidableEq K] [Algebra R K]
  (A B:R) [Invertible (3:R)] (hD:IsUnit (-16*(4*A^3+27*B^2)))

include hD in
lemma field_discriminant : IsUnit (-16*(4*(algebraMap R K A)^3+
    27*(algebraMap R K B)^2)) := by
  simpa only [map_neg,map_mul,map_add,map_pow,map_ofNat] using hD.map (algebraMap R K)

lemma division_eval (a:K) :
    (ThreeTorsionIdentity318.divisionPolynomial A B).eval₂ (algebraMap R K) a=
      (ThreeTorsionIdentity318.divisionPolynomial (algebraMap R K A)
        (algebraMap R K B)).eval a := by
  simp only [ThreeTorsionIdentity318.divisionPolynomial,eval₂_sub,eval₂_add,eval₂_mul,
    eval₂_pow,eval₂_X,eval₂_C,eval₂_ofNat,eval_sub,eval_add,eval_mul,eval_pow,eval_X,
    eval_C,eval_ofNat,map_mul,map_ofNat,map_pow]

include hD in
/-- Over every field extension of the coefficient ring, the literal
rank-eight algebra's solution predicate is exactly nonzero order-three
elliptic points. This is not merely a count of geometric roots. -/
theorem solution_iff_order_three (a b:K) :
    ((ShortThreeTorsion318.polynomial A B).eval₂ (algebraMap R K) a=0 ∧
      b^2=a^3+algebraMap R K A*a+algebraMap R K B) ↔
    ∃h:(ThreeTorsionPoints318.curve (algebraMap R K A) (algebraMap R K B)).toAffine.Nonsingular a b,
      addOrderOf (WeierstrassCurve.Affine.Point.some a b h)=3 := by
  have hd:=field_discriminant (K:=K) A B hD
  constructor
  · rintro ⟨ha,hb⟩
    have he:(ThreeTorsionPoints318.curve (algebraMap R K A)
        (algebraMap R K B)).toAffine.Equation a b := by
      simpa [WeierstrassCurve.Affine.equation_iff,ThreeTorsionPoints318.curve,
        TwoTorsionPoints318.curve] using hb
    have hΔ:(ThreeTorsionPoints318.curve (algebraMap R K A) (algebraMap R K B)).Δ≠0:=by
      rw [TwoTorsionPoints318.discriminant]
      exact hd.ne_zero
    have h:=((ThreeTorsionPoints318.curve (algebraMap R K A)
      (algebraMap R K B)).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp he
    refine ⟨h,(ThreeTorsionPoints318.root_iff_order_three _ _ hd h).mp ?_⟩
    have hr:=(ThreeTorsionFunctor318.normalized_eval_iff A B a).mp ha
    rwa [division_eval] at hr
  · rintro ⟨h,ho⟩
    refine ⟨?_,ThreeTorsionPoints318.equation _ _ h⟩
    apply (ThreeTorsionFunctor318.normalized_eval_iff A B a).mpr
    rw [division_eval]
    exact (ThreeTorsionPoints318.root_iff_order_three _ _ hd h).mpr ho

end ThreeTorsionFieldPoints318
