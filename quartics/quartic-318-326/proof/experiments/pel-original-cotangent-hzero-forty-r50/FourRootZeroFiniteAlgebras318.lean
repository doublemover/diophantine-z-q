module
public import FourRootActualDedekind318
public import FourRootDerivativeIdealRegular318
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.Jacobson.Artinian
public section
noncomputable section
namespace FourRootZeroFiniteAlgebras318
open FourRootDerivativeZeroIdeals318
/-- A regular principal quotient of a finite-type one-dimensional
Noetherian algebra is finite over the ground Jacobson ring. Both the
actual quotient and its original scalar action are retained. -/
theorem finite_principal {k A : Type*} [CommRing k] [IsJacobsonRing k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    (a : A) (ha : a ∈ nonZeroDivisors A) :
    Module.Finite k (A ⧸ Ideal.span {a}) := by
  letI : IsFiniteLength A (A ⧸ Ideal.span {a}) :=
    isFiniteLength_quotient_span_singleton A ha
  letI : IsArtinianRing (A ⧸ Ideal.span {a}) := isArtinian_of_tower A inferInstance
  exact Module.finite_of_isArtinianRing k (A ⧸ Ideal.span {a})
variable (b : Fin 4 → ℂ) (hb : Function.Injective b)
/-- Finite-dimensionality of the SAME full finite zero quotient. This
uses actual regularity of its original generator, not radical replacement. -/
theorem finite_zero : Module.Finite ℂ
    (FourRootAffineCoordinateRing318.Ring b ⧸ finiteIdeal b) := by
  letI := FourRootActualDedekind318.finite_dedekind b hb
  exact finite_principal (k := ℂ) (finiteGenerator b)
    (FourRootDerivativeIdealRegular318.finite_regular b hb)
/-- The whole reciprocal quotient is finite, retaining all infinity
centers and all original finite branch points lying in that chart. -/
theorem infinity_zero : Module.Finite ℂ
    (FourRootInfinityCoordinateRing318.Ring b ⧸ infinityIdeal b) := by
  letI := FourRootActualDedekind318.infinity_dedekind b hb
  exact finite_principal (k := ℂ) (infinityGenerator b)
    (FourRootDerivativeIdealRegular318.infinity_regular b hb)
end FourRootZeroFiniteAlgebras318
