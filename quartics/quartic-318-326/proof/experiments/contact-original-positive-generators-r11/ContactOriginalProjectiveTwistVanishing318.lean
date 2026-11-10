module
public import ContactOriginalPositiveProjectiveComparison318
public import OriginalTensorPowerCongruence318
public import ContactOriginalFixedPowerVanishing318
public section
noncomputable section
namespace ContactOriginalProjectiveTwistVanishing318
open AlgebraicGeometry CategoryTheory LineSheafClass318
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- Actual tensoring by powers of the ORIGINAL projective O(1) pullback,
whose underlying sheaf is unchanged from the old geometric construction. -/
def object (n : ℕ) : (ContactProjectiveModel318.model c).Modules :=
  IntrinsicTensorSheaf318.tensor L.object
    (FramedLineTensorPower318.object (ContactProjectiveLinePullback318.line c) n)

def comparison (n : ℕ) : object c L n ≅
    (LineSheafTensor318.line L
      (LineSheafTensorPower318.line (ContactOriginalTwistingLine318.line c 1) n)).object :=
  TensorSheafFunctor318.congr (Iso.refl L.object)
    (OriginalTensorPowerCongruence318.iso (ContactOriginalPositiveProjectiveComparison318.iso c) n)

/-- The old derived H1 comparison induced by the actual projective-line
comparison, with no new vector space or transported cohomology action. -/
def cohomologyIso (n : ℕ) :
    Sheaf.H ((SheafOfModules.toSheaf (ContactProjectiveModel318.model c).ringCatSheaf).obj
      (object c L n)) 1 ≃+
    OriginalLineMayerVietorisQuotient318.H1
      (LineSheafTensor318.line L
        (LineSheafTensorPower318.line (ContactOriginalTwistingLine318.line c 1) n)) :=
  ((Sheaf.functorH _ 1).mapIso
    ((SheafOfModules.toSheaf (ContactProjectiveModel318.model c).ringCatSheaf).mapIso
      (comparison c L n))).addCommGroupIsoToAddEquiv

/-- Genuine eventual original derived H1 vanishing after twisting any
original line by powers of the original projective O(1) pullback. This is
an objectwise theorem, not a family-uniform or representability assertion. -/
theorem exists_vanishing_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ x : Sheaf.H ((SheafOfModules.toSheaf (ContactProjectiveModel318.model c).ringCatSheaf).obj
      (object c L n)) 1, x = 0 := by
  obtain ⟨N,hN⟩ := ContactOriginalFixedPowerVanishing318.exists_vanishing_bound c L
  refine ⟨N,fun n hn x => ?_⟩
  apply (cohomologyIso c L n).injective
  rw [map_zero]
  exact hN n hn (cohomologyIso c L n x)
end ContactOriginalProjectiveTwistVanishing318
