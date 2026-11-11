module
public import PolynomialRelativeCotangentFrame318
public import Mathlib.LinearAlgebra.Isomorphisms
public section
noncomputable section
namespace PolynomialRelativeCotangentQuotient318
open Polynomial KaehlerDifferential PolynomialRelativeCotangentFrame318
variable {R S:Type*} [CommRing R] [CommRing S]
  [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
variable (e:KaehlerDifferential R S≃ₗ[S]S)
/-- The actual transitivity quotient, with its original normalized
coefficient, is the relative Kähler module itself. This is an actual
linear equivalence, not only equality of annihilators or supports. -/
@[expose] def quotientEquiv:
    (S⧸(Ideal.span {coefficient e}:Ideal S))≃ₗ[S]KaehlerDifferential R[X] S:=
  (Submodule.quotEquivOfEq _ _ (kernel e).symm).trans
    ((quotientMap e).quotKerEquivOfSurjective (quotient_surjective e))
@[simp] theorem quotientEquiv_mk (s:S):
    quotientEquiv e (Ideal.Quotient.mk (Ideal.span {coefficient e}) s)=
      KaehlerDifferential.map R R[X] S S (e.symm s):=by
  simp only [quotientEquiv,LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl
/-- Every original differential retains its actual coefficient under
this quotient comparison. -/
theorem quotientEquiv_differential (s:S):
    quotientEquiv e (Ideal.Quotient.mk (Ideal.span {coefficient e}) (e (D R S s)))=
      D R[X] S s:=by
  rw [quotientEquiv_mk,LinearEquiv.symm_apply_apply,KaehlerDifferential.map_D]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
theorem quotientEquiv_symm_differential (s:S):
    (quotientEquiv e).symm (D R[X] S s)=
      Ideal.Quotient.mk (Ideal.span {coefficient e}) (e (D R S s)):=by
  apply (quotientEquiv e).injective
  rw [LinearEquiv.apply_symm_apply,quotientEquiv_differential]
/-- Naming a proved coefficient changes neither the quotient map nor
its normalization. -/
@[expose] def coefficientEquiv (c:S) (hc:coefficient e=c):
    (S⧸(Ideal.span {c}:Ideal S))≃ₗ[S]KaehlerDifferential R[X] S:=
  (Submodule.quotEquivOfEq _ _ (congrArg (fun x:S=>(Ideal.span {x}:Ideal S)) hc.symm)).trans
    (quotientEquiv e)
@[simp] theorem coefficientEquiv_mk (c:S) (hc:coefficient e=c) (s:S):
    coefficientEquiv e c hc (Ideal.Quotient.mk (Ideal.span {c}) s)=
      KaehlerDifferential.map R R[X] S S (e.symm s):=by
  change quotientEquiv e
    (Ideal.Quotient.mk (Ideal.span {coefficient e}) s) = _
  exact quotientEquiv_mk e s
theorem coefficientEquiv_differential (c:S) (hc:coefficient e=c) (s:S):
    coefficientEquiv e c hc (Ideal.Quotient.mk (Ideal.span {c}) (e (D R S s)))=
      D R[X] S s:=by
  rw [coefficientEquiv_mk,LinearEquiv.symm_apply_apply,KaehlerDifferential.map_D]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
end PolynomialRelativeCotangentQuotient318
