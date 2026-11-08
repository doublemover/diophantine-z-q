module
public import ThreeRootScaling318
public section
noncomputable section
namespace ThreeXAlgebraPoints318
open Polynomial ThreeTorsionAlgebra318
set_option maxHeartbeats 0
variable {R K : Type*} [CommRing R] [Field K] [DecidableEq K] [Algebra R K]
  (A B : R) [Invertible (3:R)]

lemma eval_equiv (x : K) :
    (ShortThreeTorsion318.polynomial A B).eval₂ (algebraMap R K) x=0 ↔
      (ThreeTorsionIdentity318.divisionPolynomial (algebraMap R K A)
        (algebraMap R K B)).eval x=0 := by
  rw [ThreeTorsionFunctor318.normalized_eval_iff,
    ThreeTorsionFieldPoints318.division_eval]

@[expose] def toRoot (f : XRing A B →ₐ[R] K) :
    ThreeRootScaling318.Roots (algebraMap R K A) (algebraMap R K B) :=
  ⟨f (AdjoinRoot.root (ShortThreeTorsion318.polynomial A B)), (eval_equiv A B _).mp (by
    have he := congrArg f (AdjoinRoot.mk_self (f:=ShortThreeTorsion318.polynomial A B))
    rw [←AdjoinRoot.aeval_eq,←Polynomial.aeval_algHom_apply,map_zero] at he
    exact he)⟩

@[expose] def toHom (x : ThreeRootScaling318.Roots (algebraMap R K A) (algebraMap R K B)) :
    XRing A B →ₐ[R] K :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R K) x.val ((eval_equiv A B x.val).mpr x.property)

/-- Exact universal-property identification of the literal quartic algebra's
field points with the actual third-division polynomial roots. -/
@[expose] def rootEquiv : (XRing A B →ₐ[R] K) ≃
    ThreeRootScaling318.Roots (algebraMap R K A) (algebraMap R K B) where
  toFun := toRoot A B
  invFun := toHom A B
  left_inv f := by
    apply AdjoinRoot.algHom_ext
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  right_inv x := by
    apply Subtype.ext
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

end ThreeXAlgebraPoints318
