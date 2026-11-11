module
public import Mathlib.Algebra.Polynomial.Laurent
public section
noncomputable section
namespace LaurentUnitPoints318
open LaurentPolynomial
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
local notation "L" => LaurentPolynomial B
variable (S : Type u) [CommRing S] [Algebra R S]

@[expose] def unit : Lˣ := Units.ofInvertible (T 1)
lemma unit_val : (unit B:L)=T 1 := rfl
@[expose] def forward (a : L →ₐ[R] S) : Sˣ × (B →ₐ[R] S) :=
  (Units.map a.toMonoidHom (unit B),a.comp (IsScalarTower.toAlgHom R B L))
@[expose] def backward (p : Sˣ × (B →ₐ[R] S)) : L →ₐ[R] S where
  __ := LaurentPolynomial.eval₂ p.2.toRingHom p.1
  commutes' r := by
    rw [LaurentPolynomial.algebraMap_apply]
    change LaurentPolynomial.eval₂ p.2.toRingHom p.1 (C (algebraMap R B r))=algebraMap R S r
    rw [LaurentPolynomial.eval₂_C]
    exact p.2.commutes r
lemma backward_C (p : Sˣ × (B →ₐ[R] S)) (b : B) : backward R B S p (C b)=p.2 b :=
  LaurentPolynomial.eval₂_C _ _ _
lemma backward_T (p : Sˣ × (B →ₐ[R] S)) : backward R B S p (T 1)=(p.1:S) := by
  change LaurentPolynomial.eval₂ p.2.toRingHom p.1 (T 1)=(p.1:S)
  rw [LaurentPolynomial.eval₂_T,zpow_one]

/-- The literal Laurent algebra represents a coefficient unit and an
original B-point. The inverse proof checks the actual polynomial C and X
inside the Laurent localization, including every negative exponent. -/
@[expose] def points : (L →ₐ[R] S) ≃ Sˣ × (B →ₐ[R] S) where
  toFun := forward R B S
  invFun := backward R B S
  left_inv a := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial B))
    apply Polynomial.ringHom_ext
    · intro b
      change backward R B S (forward R B S a) (Polynomial.toLaurent (Polynomial.C b))=
        a (Polynomial.toLaurent (Polynomial.C b))
      rw [Polynomial.toLaurent_C,backward_C]
      rfl
    · change backward R B S (forward R B S a) (Polynomial.toLaurent Polynomial.X)=
        a (Polynomial.toLaurent Polynomial.X)
      rw [Polynomial.toLaurent_X,backward_T]
      rfl
  right_inv p := by
    apply Prod.ext
    · apply Units.ext
      change backward R B S p (T 1)=(p.1:S)
      exact backward_T R B S p
    · apply AlgHom.ext
      intro b
      exact backward_C R B S p b

variable (T' : Type u) [CommRing T'] [Algebra R T'] (g : S →ₐ[R] T')
lemma unit_natural (a : L →ₐ[R] S) : (points R B T' (g.comp a)).1=
    Units.map g.toMonoidHom (points R B S a).1 := rfl
lemma coefficient_natural (a : L →ₐ[R] S) : (points R B T' (g.comp a)).2=
    g.comp (points R B S a).2 := rfl
end LaurentUnitPoints318
