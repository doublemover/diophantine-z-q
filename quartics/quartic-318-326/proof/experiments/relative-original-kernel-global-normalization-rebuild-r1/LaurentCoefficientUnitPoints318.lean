module
public import LaurentUnitPoints318
public section
noncomputable section
namespace LaurentCoefficientUnitPoints318
open LaurentPolynomial
universe u
variable {R S T' : Type u} [CommRing R] [CommRing S] [CommRing T']
variable (r : R →+* S)
/-- Ring maps with the ACTUAL coefficient map fixed, without implicit algebra instances. -/
abbrev Points := {a : LaurentPolynomial R →+* S // a.comp C=r}
@[expose] def value (a : Points r) : Sˣ :=
  Units.map a.val.toMonoidHom (LaurentUnitPoints318.unit R)
@[expose] def lift (u : Sˣ) : Points r :=
  ⟨eval₂ r u,by ext x; exact eval₂_C r u x⟩
lemma value_lift (u : Sˣ) : value r (lift r u)=u := by
  apply Units.ext
  change eval₂ r u (T 1)=(u:S)
  rw [eval₂_T,zpow_one]
@[expose] def equivalence : Points r ≃ Sˣ where
  toFun := value r
  invFun := lift r
  left_inv a := by
    apply Subtype.ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
    apply Polynomial.ringHom_ext
    · intro x
      change eval₂ r (value r a) (Polynomial.toLaurent (Polynomial.C x))=a.val (Polynomial.toLaurent (Polynomial.C x))
      rw [Polynomial.toLaurent_C,eval₂_C]
      exact (RingHom.congr_fun a.property x).symm
    · change eval₂ r (value r a) (Polynomial.toLaurent Polynomial.X)=a.val (Polynomial.toLaurent Polynomial.X)
      rw [Polynomial.toLaurent_X,eval₂_T,zpow_one] <;> rfl
  right_inv := value_lift r
lemma natural (g : S →+* T') (a : Points r) :
    value (g.comp r) ⟨g.comp a.val,by rw [RingHom.comp_assoc,a.property]⟩=
      Units.map g.toMonoidHom (value r a) := rfl

end LaurentCoefficientUnitPoints318
