module
public import FiniteNormalBaseMonogenicSuborder318
public section
noncomputable section
namespace IntegralElementBaseCutoff318
open Polynomial
variable (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]

/-- The literal constant coefficient of the actual minimal polynomial
of a nonzero integral element is nonzero. -/
lemma constant_ne_zero (a : A) (hi : IsIntegral R a) (ha : a ≠ 0) :
    (minpoly R a).coeff 0 ≠ 0 := by
  intro hzero
  have hx : (X : R[X]) ∣ minpoly R a := Polynomial.X_dvd_iff.mpr hzero
  have hp : minpoly R a = X :=
    Polynomial.eq_of_monic_of_associated (minpoly.monic hi) Polynomial.monic_X
      (associated_of_dvd_dvd ((Polynomial.irreducible_X).dvd_symm (minpoly.irreducible hi) hx) hx)
  have h := minpoly.aeval R a
  rw [hp,Polynomial.aeval_X] at h
  exact ha h

/-- Above the nonvanishing of the actual base constant coefficient,
EVERY whole-algebra evaluation has nonzero value at the original
element. The polynomial relation, not a selected component, gives this. -/
lemma value_ne_zero {K : Type*} [Field K] (a : A)
    (v : R →+* K) (f : A →+* K) (hs : f.comp (algebraMap R A) = v)
    (hb : v ((minpoly R a).coeff 0) ≠ 0) : f a ≠ 0 := by
  intro hz
  have h := congrArg f (minpoly.aeval R a)
  change f ((minpoly R a).eval₂ (algebraMap R A) a) = f 0 at h
  rw [Polynomial.hom_eval₂,hs,hz,map_zero,←Polynomial.eval_map,Polynomial.eval_zero,Polynomial.coeff_map] at h
  exact hb h

/-- A genuine nonzero base cutoff is constructed from any nonzero
integral original denominator. No unit, normality or freeness of the
whole source is assumed. -/
theorem exists_cutoff (a : A) (hi : IsIntegral R a) (ha : a ≠ 0) :
    ∃ b : R, b ≠ 0 ∧
      ∀ (v : R →+* ℂ) (f : A →+* ℂ),
        f.comp (algebraMap R A) = v → v b ≠ 0 → f a ≠ 0 :=
  ⟨(minpoly R a).coeff 0,constant_ne_zero R A a hi ha,
    fun v f hs hb => value_ne_zero R A a v f hs hb⟩
end IntegralElementBaseCutoff318
