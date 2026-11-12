module
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public section
namespace PrimeQuotientEmpty318
open AlgebraicGeometry
universe u
variable (A : Type u) [CommRing A] (I : Ideal A)
/-- Empty spectrum of the WHOLE quotient is equivalent to the actual ideal
being the unit ideal, over every ring, including nonreduced and zero rings. -/
lemma iff_top : IsEmpty ↑(Spec (CommRingCat.of (A ⧸ I))) ↔ I=⊤ :=
  PrimeSpectrum.isEmpty_iff_subsingleton.trans Ideal.Quotient.subsingleton_iff
end PrimeQuotientEmpty318
