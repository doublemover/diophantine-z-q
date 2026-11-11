module
public import ContactRelativeTwistPowers318
public import ContactHOneVanishingBaseChange318
public section
noncomputable section
namespace ContactRelativeFixedPowerVanishing318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeGeometricTwist318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
@[expose] def twistedPower (n : ℕ) :=
  LineSheafTensor318.line L (LineSheafTensorPower318.line (line R c 1) n)
@[expose] def cohomologyIso (n : ℕ) :
    NonreducedLineMayerVietoris318.H1 (twistedPower R c L n) ≃+
      NonreducedLineMayerVietoris318.H1 (twist R c L (n : ℤ)) :=
  ((Sheaf.functorH _ 1).mapIso ((SheafOfModules.toSheaf (curve R c).ringCatSheaf).mapIso
    (ContactRelativeTwistPowers318.twistedPowerIso R c L n))).addCommGroupIsoToAddEquiv

/-- Relative geometric vanishing now uses powers of one FIXED actual
line, for every original L on every coefficient test. -/
theorem exists_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ x : NonreducedLineMayerVietoris318.H1 (twistedPower R c L n), x = 0 := by
  obtain ⟨N,hN⟩ := ContactRelativeGeometricVanishing318.exists_bound R c L
  refine ⟨N,fun n hn x => ?_⟩
  apply (cohomologyIso R c L n).injective
  rw [map_zero]
  exact hN n hn (cohomologyIso R c L n x)

/-- One bound for original fixed-line powers remains valid after every
further base change on the actual pulled-back geometric objects. -/
theorem exists_universal_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S),
    ∀ x : NonreducedLineMayerVietoris318.H1
      (ContactOriginalDerivedCoefficientMap318.pulled R S f c (twistedPower R c L n)), x = 0 := by
  obtain ⟨N,hN⟩ := exists_bound R c L
  exact ⟨N,fun n hn S _ f x => ContactHOneVanishingBaseChange318.vanishes R c
    (twistedPower R c L n) (hN n hn) S f x⟩
end ContactRelativeFixedPowerVanishing318
