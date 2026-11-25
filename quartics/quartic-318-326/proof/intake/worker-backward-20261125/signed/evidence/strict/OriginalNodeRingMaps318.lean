module
public import OriginalSplitNodeCoordinates318
import all OriginalSplitNodeCoordinates318
public section
noncomputable section

namespace OriginalNodeRingMaps318

open Polynomial OriginalSplitNodeCoordinates318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]

/-- Ring map on the same split node T[x,y]/(xy−π), with both axes
and coefficients preserved explicitly. -/
@[expose] def eval (q : R) (x y : T) (h : y*x=algebraMap R T q) : Node q →ₐ[R] T :=
  AdjoinRoot.liftAlgHom (equation q) (aeval y) x (by
    rw [equation,eval₂_sub,eval₂_mul,eval₂_C,eval₂_X,eval₂_C]
    apply sub_eq_zero.mpr
    change (aeval y : R[X] →ₐ[R] T) X * x = (aeval y : R[X] →ₐ[R] T) (C q)
    rw [aeval_X,aeval_C]
    exact h)

theorem eval_x (q : R) (x y : T) (h : y*x=algebraMap R T q) :
    eval q x y h (xAxis q)=x :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem eval_y (q : R) (x y : T) (h : y*x=algebraMap R T q) :
    eval q x y h (yAxis q)=y :=
  (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (aeval_X y)

theorem ext {q : R} {a b : Node q →ₐ[R] T}
    (hx : a (xAxis q)=b (xAxis q)) (hy : a (yAxis q)=b (yAxis q)) : a=b := by
  apply AdjoinRoot.algHom_ext' _ hx
  exact Polynomial.algHom_ext hy

theorem node_relation (q : R) :
    yAxis q*xAxis q=algebraMap R (Node q) q := by
  apply sub_eq_zero.mp
  change AdjoinRoot.mk (equation q) (C (X : R[X])) *
      AdjoinRoot.mk (equation q) X -
      AdjoinRoot.mk (equation q) (C (C q)) = 0
  rw [←map_mul,←map_sub]
  exact AdjoinRoot.mk_self

end OriginalNodeRingMaps318
#print axioms OriginalNodeRingMaps318.eval
#print axioms OriginalNodeRingMaps318.node_relation
