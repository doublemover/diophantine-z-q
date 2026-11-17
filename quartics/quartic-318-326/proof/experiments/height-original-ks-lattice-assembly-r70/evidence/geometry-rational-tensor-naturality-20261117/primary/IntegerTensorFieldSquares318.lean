module
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public section
noncomputable section
namespace IntegerTensorFieldSquares318
open scoped TensorProduct
variable (R : Type*) [CommRing R]
abbrev Fiber := R ⊗[ℤ] ℚ
abbrev denominators := Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ)

variable {R} {L : Type*} [Field L] [CharZero L]

/-- Only nonzero integer coefficients are inverted. -/
theorem field_units (f : R →+* L) (s : denominators R) : IsUnit (f s) := by
  obtain ⟨n, hn, he⟩ := s.property
  change IsUnit (f s.val)
  rw [← he]
  change IsUnit (f (n : R))
  rw [map_intCast]
  exact IsUnit.mk0 _ (Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero hn))

@[expose] def embedding (f : R →+* L) : Fiber R →+* L :=
  IsLocalization.lift (M := denominators R) (S := Fiber R) (field_units f)

theorem embedding_base (f : R →+* L) (r : R) :
    embedding f (algebraMap R (Fiber R) r) = f r :=
  IsLocalization.lift_eq (M := denominators R) (S := Fiber R) (field_units f) r

theorem embedding_injective (f : R →+* L) (hf : Function.Injective f) :
    Function.Injective (embedding f) := by
  apply (IsLocalization.lift_injective_iff (M := denominators R)
    (S := Fiber R) (field_units f)).mpr
  intro x y
  constructor
  · intro h
    have := congrArg (embedding f) h
    simpa only [embedding_base] using this
  · intro h
    exact congrArg (algebraMap R (Fiber R)) (hf h)

variable {S : Type*} [CommRing S]

theorem maps_denominators (g : R →+* S) :
    denominators R ≤ (denominators S).comap g := by
  rintro x ⟨n, hn, rfl⟩
  exact ⟨n, hn, by simp⟩

/-- The coefficient-localized version of the displayed original map. -/
@[expose] def rationalMap (g : R →+* S) : Fiber R →+* Fiber S :=
  IsLocalization.map (M := denominators R) (T := denominators S)
    (S := Fiber R) (Fiber S) g (maps_denominators g)

theorem rationalMap_base (g : R →+* S) (r : R) :
    rationalMap g (algebraMap R (Fiber R) r) = algebraMap S (Fiber S) (g r) :=
  IsLocalization.map_eq (M := denominators R) (T := denominators S)
    (S := Fiber R) (Q := Fiber S) (maps_denominators g) r

/-- An actual field square survives coefficient rationalization. Neither
an isomorphism of abstract fields nor equality of different parameter actions
is used. -/
theorem embedding_square (f : R →+* L) (h : S →+* L) (g : R →+* S)
    (hg : h.comp g = f) : (embedding h).comp (rationalMap g) = embedding f := by
  apply IsLocalization.ringHom_ext (denominators R)
  ext r
  change embedding h (rationalMap g (algebraMap R (Fiber R) r)) =
    embedding f (algebraMap R (Fiber R) r)
  rw [rationalMap_base, embedding_base, embedding_base]
  exact RingHom.congr_fun hg r

end IntegerTensorFieldSquares318
