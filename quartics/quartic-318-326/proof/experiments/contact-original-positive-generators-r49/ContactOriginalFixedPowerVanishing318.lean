module
public import ContactOriginalTwistPower318
public section
noncomputable section
namespace ContactOriginalFixedPowerVanishing318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalTwistingLine318
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- Exact functorial comparison of the SAME original derived cohomology
carriers, induced by the actual reconstructed tensor-power isomorphism. -/
def cohomologyIso (n : ℕ) :
    OriginalLineMayerVietorisQuotient318.H1
      (LineSheafTensor318.line L (LineSheafTensorPower318.line (line c 1) n)) ≃+
    OriginalLineMayerVietorisQuotient318.H1 (twist c L (n : ℤ)) :=
  ((Sheaf.functorH _ 1).mapIso
    ((SheafOfModules.toSheaf (ContactProjectiveModel318.model c).ringCatSheaf).mapIso
      (ContactOriginalTwistPower318.twistedPowerIso c L n))).addCommGroupIsoToAddEquiv

/-- Its map is literally the old induced coefficient map on derived H1. -/
lemma cohomologyIso_apply (n : ℕ)
    (x : OriginalLineMayerVietorisQuotient318.H1
      (LineSheafTensor318.line L (LineSheafTensorPower318.line (line c 1) n))) :
    cohomologyIso c L n x = Sheaf.H.map
      ((SheafOfModules.toSheaf (ContactProjectiveModel318.model c).ringCatSheaf).map
        (ContactOriginalTwistPower318.twistedPowerIso c L n).hom) 1 x := rfl

/-- Eventual original derived H1 vanishing for actual tensor powers of one
FIXED positive line, for every old line L. No ample/projective naming or
family-uniform bound is inferred from this objectwise theorem. -/
theorem exists_vanishing_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ x : OriginalLineMayerVietorisQuotient318.H1
      (LineSheafTensor318.line L (LineSheafTensorPower318.line (line c 1) n)), x = 0 := by
  obtain ⟨N,hN⟩ := ContactOriginalPositiveTwistHOne318.exists_vanishing_bound c L
  refine ⟨N,fun n hn x => ?_⟩
  apply (cohomologyIso c L n).injective
  rw [map_zero]
  exact hN n hn (cohomologyIso c L n x)
end ContactOriginalFixedPowerVanishing318
