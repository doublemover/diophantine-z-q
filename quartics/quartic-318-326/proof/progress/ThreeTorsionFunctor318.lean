module
public import ThreeTorsionAlgebra318
public section
noncomputable section
namespace ThreeTorsionFunctor318
open Polynomial ThreeTorsionAlgebra318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B:R) [Invertible (3:R)] (hD:IsUnit (-16*(4*A^3+27*B^2)))

lemma normalized_eval_iff (a:S) :
    (ShortThreeTorsion318.polynomial A B).eval₂ (algebraMap R S) a=0 ↔
      (ThreeTorsionIdentity318.divisionPolynomial A B).eval₂ (algebraMap R S) a=0 := by
  rw [←ShortThreeTorsion318.scalar_identity,eval₂_mul,eval₂_C]
  exact ((isUnit_of_invertible (3:R)).map (algebraMap R S)).mul_right_eq_zero.symm

@[expose] def Solutions := {p:S×S //
  (ShortThreeTorsion318.polynomial A B).eval₂ (algebraMap R S) p.1=0 ∧
    p.2^2=p.1^3+algebraMap R S A*p.1+algebraMap R S B}

@[expose] def xHom (p:Solutions (S:=S) A B) : XRing A B→ₐ[R]S :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R S) p.val.1 p.property.1

lemma xHom_cubic (p:Solutions (S:=S) A B) :
    xHom A B p (cubic A B)=p.val.1^3+algebraMap R S A*p.val.1+algebraMap R S B := by
  simp only [xHom,cubic,AdjoinRoot.liftAlgHom_mk,ShortTwoTorsion318.polynomial,
    eval₂_add,eval₂_pow,eval₂_X,eval₂_mul,eval₂_C]
  rfl

@[expose] def toHom (p:Solutions (S:=S) A B) : Ring A B hD→ₐ[R]S :=
  AdjoinRoot.liftAlgHom (EvenContactEtale318.polynomial (cubicUnit A B hD))
    (xHom A B p) p.val.2 (by
      simp only [EvenContactEtale318.polynomial,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C]
      change p.val.2^2-xHom A B p (cubicUnit A B hD:XRing A B)=0
      rw [cubicUnit_val,xHom_cubic]
      exact sub_eq_zero.mpr p.property.2)

lemma toHom_x (p:Solutions (S:=S) A B) : toHom A B hD p (x A B hD)=p.val.1 := by
  simp only [toHom,x,AdjoinRoot.algebraMap_eq,AdjoinRoot.liftAlgHom_of,xHom,
    AdjoinRoot.liftAlgHom_root]
lemma toHom_y (p:Solutions (S:=S) A B) : toHom A B hD p (y A B hD)=p.val.2 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

lemma hom_ext (f g:Ring A B hD→ₐ[R]S)
    (hx:f (x A B hD)=g (x A B hD)) (hy:f (y A B hD)=g (y A B hD)) : f=g := by
  apply AdjoinRoot.algHom_ext'
  · apply AdjoinRoot.algHom_ext
    exact hx
  · exact hy

lemma x_relation : aeval (x A B hD) (ShortThreeTorsion318.polynomial A B)=0 := by
  let f:=IsScalarTower.toAlgHom R (XRing A B) (Ring A B hD)
  have hh:=congrArg f (AdjoinRoot.mk_self (f:=ShortThreeTorsion318.polynomial A B))
  rw [←AdjoinRoot.aeval_eq,←Polynomial.aeval_algHom_apply,map_zero] at hh
  exact hh

@[expose] def ofHom (f:Ring A B hD→ₐ[R]S) : Solutions (S:=S) A B :=
  ⟨(f (x A B hD),f (y A B hD)),by
    constructor
    · have hh:=congrArg f (x_relation A B hD)
      rw [←Polynomial.aeval_algHom_apply,map_zero] at hh
      exact hh
    · have hh:=congrArg f (equation A B hD)
      simpa only [map_pow,map_add,map_mul,AlgHom.commutes] using hh⟩

/-- The actual rank-eight algebra represents the two literal equations over
all coefficient algebras, including algebras with nilpotents. -/
@[expose] def solutionEquiv : (Ring A B hD→ₐ[R]S)≃Solutions (S:=S) A B where
  toFun:=ofHom A B hD
  invFun:=toHom A B hD
  left_inv f:=hom_ext A B hD _ _ (toHom_x A B hD _) (toHom_y A B hD _)
  right_inv p:=by
    apply Subtype.ext
    exact Prod.ext (toHom_x A B hD p) (toHom_y A B hD p)

end ThreeTorsionFunctor318
