module
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.Algebra.Polynomial.Div
public section
noncomputable section
namespace ActualPrimitiveQuotient318
open Polynomial
variable {B L F K : Type*} [CommRing B] [CommRing L] [Field F] [Field K]
  [Algebra F K]

/-- A monic equation that becomes the actual minimal polynomial in an
injective coefficient field has no extra quotient kernel. The square
uses the original source-field map, not a newly chosen scalar action. -/
theorem lift_injective (u : B →+* F) (hu : Function.Injective u)
    (g : B →+* L) (φ : L →+* K) (β : L) (α : K)
    (hs : φ.comp g = (algebraMap F K).comp u) (hβ : φ β = α)
    (Q : Polynomial B) (hm : Q.Monic) (hQ : Q.map u = minpoly F α)
    (hr : Q.eval₂ g β = 0) :
    Function.Injective (AdjoinRoot.lift g β hr) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective (g := Q) z
  apply AdjoinRoot.mk_eq_zero.mpr
  apply (Polynomial.map_dvd_map u hu hm).mp
  rw [hQ]
  apply minpoly.dvd F α
  have he : P.eval₂ g β = 0 := by
    simpa only [AdjoinRoot.lift_mk] using hz
  have he' := congrArg φ he
  rw [Polynomial.hom_eval₂, hs, hβ, map_zero] at he'
  simpa only [Polynomial.aeval_def, Polynomial.eval₂_map] using he'

/-- Full polynomial evaluation surjectivity supplies the other half of
an actual quotient/order equivalence, rather than equality of fields. -/
theorem lift_surjective (g : B →+* L) (β : L) (Q : Polynomial B)
    (hr : Q.eval₂ g β = 0)
    (hs : Function.Surjective (Polynomial.eval₂RingHom g β)) :
    Function.Surjective (AdjoinRoot.lift g β hr) := by
  intro z
  obtain ⟨P, hP⟩ := hs z
  exact ⟨AdjoinRoot.mk Q P, (AdjoinRoot.lift_mk hr P).trans hP⟩
end ActualPrimitiveQuotient318
