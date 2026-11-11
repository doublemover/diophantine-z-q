module
public import FourRootActualOrderGalois318
public section
noncomputable section
namespace PolynomialOrderIsomorphismInertia318
variable {R S T C:Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing C]
  [Algebra R S] [Algebra R T] (e:S≃ₐ[R]T)

/-- Full actual order automorphisms are conjugated through an explicitly
base-preserving algebra equivalence, not through an unrelated field. -/
@[expose] def conjugation:(S≃ₐ[R]S)≃(T≃ₐ[R]T) where
  toFun g:=e.symm.trans (g.trans e)
  invFun g:=e.trans (g.trans e.symm)
  left_inv g:=by ext x;simp only [AlgEquiv.trans_apply,AlgEquiv.symm_apply_apply]
  right_inv g:=by ext x;simp only [AlgEquiv.trans_apply,AlgEquiv.apply_symm_apply]

lemma invariant (h:Algebra.IsInvariant R T (T≃ₐ[R]T)):
    Algebra.IsInvariant R S (S≃ₐ[R]S):=by
  constructor
  intro x hx
  have ht:∀g:T≃ₐ[R]T,g (e x)=e x:=by
    intro g
    have hh:=congrArg e (hx (e.trans (g.trans e.symm)))
    simpa only [AlgEquiv.trans_apply,AlgEquiv.apply_symm_apply] using hh
  obtain ⟨r,hr⟩:=h.1 (e x) ht
  refine ⟨r,?_⟩
  apply e.injective
  rw [AlgEquiv.commutes]
  exact hr

lemma kernel_membership (f:S→+*C) (g:S≃ₐ[R]S):
    g∈(RingHom.ker f).inertia (S≃ₐ[R]S) ↔ ∀x,f (g x)=f x:=by
  rw [Ideal.mem_inertia]
  constructor
  · intro h x
    have hh:=h x
    change f (g x-x)=0 at hh
    simpa only [map_sub,sub_eq_zero] using hh
  · intro h x
    change f (g x-x)=0
    rw [map_sub,h,sub_self]

lemma inertia_iff (f:S→+*C) (g:S≃ₐ[R]S):
    g∈(RingHom.ker f).inertia (S≃ₐ[R]S) ↔
      conjugation e g∈(RingHom.ker (f.comp e.symm.toRingHom)).inertia (T≃ₐ[R]T):=by
  rw [kernel_membership,kernel_membership]
  constructor
  · intro h y
    change f (e.symm (e (g (e.symm y))))=f (e.symm y)
    rw [AlgEquiv.symm_apply_apply]
    exact h _
  · intro h x
    have hh:=h (e x)
    change f (e.symm (e (g (e.symm (e x)))))=f (e.symm (e x)) at hh
    simpa only [AlgEquiv.symm_apply_apply] using hh

@[expose] def inertiaEquivalence (f:S→+*C):
    (RingHom.ker f).inertia (S≃ₐ[R]S)≃
      (RingHom.ker (f.comp e.symm.toRingHom)).inertia (T≃ₐ[R]T):=
  (conjugation e).subtypeEquiv (inertia_iff e f)
end PolynomialOrderIsomorphismInertia318
