module
public import ThreeTorsionAlgebra318
public import MonogenicSplitEquiv318
public section
noncomputable section
namespace ThreeXScalingAlgebra318
open Polynomial
set_option maxHeartbeats 0
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B : R) [Invertible (3:R)] (s : Rˣ)

include s in
lemma cancel_scale (x : S) :
    algebraMap R S (s:R) * (algebraMap R S ((s⁻¹:Rˣ):R) * x) = x := by
  rw [←mul_assoc,←map_mul,Units.mul_inv,map_one,one_mul]

lemma eval_scale (x : S) :
    (ShortThreeTorsion318.polynomial ((s:R)^2*A) ((s:R)^3*B)).eval₂ (algebraMap R S)
      (algebraMap R S (s:R)*x) =
      (algebraMap R S (s:R))^4*(ShortThreeTorsion318.polynomial A B).eval₂ (algebraMap R S) x := by
  simp only [ShortThreeTorsion318.polynomial,eval₂_sub,eval₂_add,eval₂_mul,eval₂_pow,
    eval₂_X,eval₂_C,eval₂_ofNat,map_mul,map_pow,map_ofNat]
  ring

lemma root_eval (a b : R) : (ShortThreeTorsion318.polynomial a b).eval₂
    (algebraMap R (ShortThreeTorsion318.Ring a b))
    (AdjoinRoot.root (ShortThreeTorsion318.polynomial a b))=0 := by
  simpa only [AdjoinRoot.algebraMap_eq] using
    AdjoinRoot.eval₂_root (ShortThreeTorsion318.polynomial a b)

@[expose] def pullback : ShortThreeTorsion318.Ring ((s:R)^2*A) ((s:R)^3*B) →ₐ[R]
    ShortThreeTorsion318.Ring A B :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) (algebraMap R _ (s:R) *
    AdjoinRoot.root (ShortThreeTorsion318.polynomial A B)) (by
      change (ShortThreeTorsion318.polynomial ((s:R)^2*A) ((s:R)^3*B)).eval₂
        (algebraMap R (ShortThreeTorsion318.Ring A B)) _ = 0
      rw [eval_scale,root_eval,mul_zero])

@[expose] def inverse : ShortThreeTorsion318.Ring A B →ₐ[R]
    ShortThreeTorsion318.Ring ((s:R)^2*A) ((s:R)^3*B) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) (algebraMap R _ ((s⁻¹:Rˣ):R) *
    AdjoinRoot.root (ShortThreeTorsion318.polynomial ((s:R)^2*A) ((s:R)^3*B))) (by
      let T := ShortThreeTorsion318.Ring ((s:R)^2*A) ((s:R)^3*B)
      have he := eval_scale (S:=T) A B s (algebraMap R T ((s⁻¹:Rˣ):R) *
        AdjoinRoot.root (ShortThreeTorsion318.polynomial ((s:R)^2*A) ((s:R)^3*B)))
      rw [cancel_scale,root_eval] at he
      exact (((s.isUnit.map (algebraMap R T)).pow 4).mul_right_eq_zero).mp he.symm)

lemma pullback_root : pullback A B s
    (AdjoinRoot.root (ShortThreeTorsion318.polynomial ((s:R)^2*A) ((s:R)^3*B))) =
      algebraMap R _ (s:R)*AdjoinRoot.root (ShortThreeTorsion318.polynomial A B) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

lemma inverse_root : inverse A B s (AdjoinRoot.root (ShortThreeTorsion318.polynomial A B)) =
    algebraMap R _ ((s⁻¹:Rˣ):R)*AdjoinRoot.root
      (ShortThreeTorsion318.polynomial ((s:R)^2*A) ((s:R)^3*B)) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

lemma inverse_comp : (inverse A B s).comp (pullback A B s) = AlgHom.id R _ := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply,pullback_root,map_mul,AlgHom.commutes,inverse_root,
    AlgHom.id_apply]
  exact cancel_scale s _

lemma pullback_comp : (pullback A B s).comp (inverse A B s) = AlgHom.id R _ := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply,inverse_root,map_mul,AlgHom.commutes,pullback_root,
    AlgHom.id_apply]
  simpa only [inv_inv] using cancel_scale (S:=ShortThreeTorsion318.Ring A B) s⁻¹
    (AdjoinRoot.root (ShortThreeTorsion318.polynomial A B))

/-- The canonical x-coordinate transformation is an actual isomorphism of
quartic algebras over every coefficient ring, including rings with nilpotents. -/
@[expose] def algebraEquiv : ShortThreeTorsion318.Ring ((s:R)^2*A) ((s:R)^3*B) ≃ₐ[R]
    ShortThreeTorsion318.Ring A B :=
  AlgEquiv.ofAlgHom (pullback A B s) (inverse A B s) (pullback_comp A B s) (inverse_comp A B s)

end ThreeXScalingAlgebra318

namespace ThreeXScalingAlgebra318
open Polynomial
variable {R : Type*} [CommRing R] (A B : R) [Invertible (3:R)] (s : Rˣ)

theorem algebraEquiv_root : algebraEquiv A B s
    (AdjoinRoot.root (ShortThreeTorsion318.polynomial ((s:R)^2*A) ((s:R)^3*B))) =
      algebraMap R _ (s:R)*AdjoinRoot.root (ShortThreeTorsion318.polynomial A B) :=
  pullback_root A B s

theorem algebraEquiv_symm_root : (algebraEquiv A B s).symm
    (AdjoinRoot.root (ShortThreeTorsion318.polynomial A B)) =
      algebraMap R _ ((s⁻¹:Rˣ):R)*AdjoinRoot.root
        (ShortThreeTorsion318.polynomial ((s:R)^2*A) ((s:R)^3*B)) := inverse_root A B s

end ThreeXScalingAlgebra318
