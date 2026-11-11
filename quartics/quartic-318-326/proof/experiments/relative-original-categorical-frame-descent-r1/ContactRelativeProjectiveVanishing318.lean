module
public import ContactRelativeProjectivePositive318
public section
noncomputable section
namespace ContactRelativeProjectiveVanishing318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))

@[expose] def twistedPower (n : ℕ) : Line (curve R c) :=
  LineSheafTensor318.line L
    (LineSheafTensorPower318.line (ContactRelativeProjectivePositive318.line R c) n)

@[expose] def cohomologyIso (n : ℕ) :
    NonreducedLineMayerVietoris318.H1 (twistedPower R c L n) ≃+
    NonreducedLineMayerVietoris318.H1 (ContactRelativeFixedPowerVanishing318.twistedPower R c L n) :=
  ((Sheaf.functorH _ 1).mapIso
    ((SheafOfModules.toSheaf (curve R c).ringCatSheaf).mapIso
      (ContactRelativeProjectivePositive318.twistedPowerIso R c L n))).addCommGroupIsoToAddEquiv

/-- For EVERY original line on EVERY affine coefficient test, powers of
the actual original projective O(1) pullback eventually kill actual H1.
The geometric identification is constructed, not supplied as an assumption. -/
theorem exists_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ x : NonreducedLineMayerVietoris318.H1 (twistedPower R c L n), x = 0 := by
  obtain ⟨N,hN⟩ := ContactRelativeFixedPowerVanishing318.exists_bound R c L
  refine ⟨N,fun n hn x => ?_⟩
  apply (cohomologyIso R c L n).injective
  rw [map_zero]
  exact hN n hn (cohomologyIso R c L n x)

/-- The SAME projective-power bound survives EVERY further affine
coefficient change on the actual pulled-back original geometric objects. -/
theorem exists_universal_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S),
    ∀ x : NonreducedLineMayerVietoris318.H1
      (ContactOriginalDerivedCoefficientMap318.pulled R S f c (twistedPower R c L n)), x = 0 := by
  obtain ⟨N,hN⟩ := exists_bound R c L
  exact ⟨N,fun n hn S _ f x => ContactHOneVanishingBaseChange318.vanishes R c
    (twistedPower R c L n) (hN n hn) S f x⟩
end ContactRelativeProjectiveVanishing318
