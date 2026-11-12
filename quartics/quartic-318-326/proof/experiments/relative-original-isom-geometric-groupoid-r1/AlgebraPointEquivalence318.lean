module
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Algebra.Equiv
public section
noncomputable section
namespace AlgebraPointEquivalence318
variable (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
variable (e : ∀ (S : Type) [CommRing S] [Algebra R S], (A →ₐ[R] S) ≃ (B →ₐ[R] S))
variable (hn : ∀ (S T : Type) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (g : S →ₐ[R] T) (a : A →ₐ[R] S), e T (g.comp a)=g.comp (e S a))

@[expose] def forwardHom : A →ₐ[R] B := (e B).symm (AlgHom.id R B)
@[expose] def backwardHom : B →ₐ[R] A := e A (AlgHom.id R A)

include hn in
lemma to_from : (forwardHom R A B e).comp (backwardHom R A B e)=AlgHom.id R B := by
  have h := hn A B (forwardHom R A B e) (AlgHom.id R A)
  have hi : e B (forwardHom R A B e)=AlgHom.id R B := (e B).apply_symm_apply _
  simpa only [AlgHom.comp_id, hi, backwardHom] using h.symm

include hn in
lemma from_to : (backwardHom R A B e).comp (forwardHom R A B e)=AlgHom.id R A := by
  apply (e A).injective
  rw [hn B A (backwardHom R A B e) (forwardHom R A B e)]
  rw [show e B (forwardHom R A B e)=AlgHom.id R B from (e B).apply_symm_apply _]
  rw [AlgHom.comp_id]
  rfl

/-- Elementary algebra Yoneda: natural bijections on ALL algebra-valued
points produce actual inverse algebra maps, using only the two identity
points. This is not a geometric-point reconstruction principle. -/
@[expose] def algebraEquiv : A ≃ₐ[R] B :=
  { forwardHom R A B e with
    invFun := backwardHom R A B e
    left_inv := fun a => DFunLike.congr_fun (from_to R A B e hn) a
    right_inv := fun b => DFunLike.congr_fun (to_from R A B e hn) b }

lemma evaluate (S : Type) [CommRing S] [Algebra R S] (a : A →ₐ[R] S) :
    e S a=a.comp (algebraEquiv R A B e hn).symm.toAlgHom := by
  have h := hn A S a (AlgHom.id R A)
  simpa only [AlgHom.comp_id] using h
end AlgebraPointEquivalence318
