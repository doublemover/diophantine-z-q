module
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section
namespace ComplexPolynomialOpenPoints318
open AlgebraicGeometry CategoryTheory
variable {ι : Type}
abbrev PolynomialBase := MvPolynomial ι ℂ

/-- Literal evaluation at a complex vector on the specified principal
open, extended through its actual localization universal property. -/
@[expose] def evaluation (p : (PolynomialBase (ι := ι))) (v : ι → ℂ)
    (hv : MvPolynomial.eval v p ≠ 0) : Localization.Away p →+* ℂ :=
  IsLocalization.Away.lift p (g := MvPolynomial.eval₂Hom (RingHom.id ℂ) v)
    (isUnit_iff_ne_zero.mpr hv)

@[simp] theorem evaluation_source (p : (PolynomialBase (ι := ι))) (v : ι → ℂ)
    (hv : MvPolynomial.eval v p ≠ 0) (a : (PolynomialBase (ι := ι))) :
    evaluation p v hv (algebraMap (PolynomialBase (ι := ι)) (Localization.Away p) a) =
      MvPolynomial.eval v a :=
  IsLocalization.Away.lift_eq p (isUnit_iff_ne_zero.mpr hv) a

@[simp] theorem evaluation_constant (p : (PolynomialBase (ι := ι))) (v : ι → ℂ)
    (hv : MvPolynomial.eval v p ≠ 0) (c : ℂ) :
    evaluation p v hv (algebraMap ℂ (Localization.Away p) c) = c := by
  rw [IsScalarTower.algebraMap_apply ℂ (PolynomialBase (ι := ι)) (Localization.Away p),evaluation_source]
  exact MvPolynomial.eval_C _ _

@[expose] def point (p : (PolynomialBase (ι := ι))) (v : ι → ℂ)
    (hv : MvPolynomial.eval v p ≠ 0) :
    Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Localization.Away p)) :=
  Spec.map (CommRingCat.ofHom (evaluation p v hv))

/-- This is a point OVER the given complex field, not just an arbitrary
morphism from its underlying prime spectrum. -/
@[reassoc] theorem over_complex (p : (PolynomialBase (ι := ι))) (v : ι → ℂ)
    (hv : MvPolynomial.eval v p ≠ 0) :
    point p v hv ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (Localization.Away p))) = 𝟙 _ := by
  rw [point,←Spec.map_comp,←Spec.map_id]
  congr 1
  ext c
  exact evaluation_constant p v hv c

@[reassoc] theorem original_evaluation (p : (PolynomialBase (ι := ι))) (v : ι → ℂ)
    (hv : MvPolynomial.eval v p ≠ 0) :
    point p v hv ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (PolynomialBase (ι := ι)) (Localization.Away p))) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id ℂ) v)) := by
  rw [point,←Spec.map_comp]
  congr 1
  ext a
  exact evaluation_source p v hv a
end ComplexPolynomialOpenPoints318
