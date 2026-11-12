module
public import ContactCanonicalHOneBaseChange318
public section
noncomputable section
namespace ContactDerivedCoefficientSemilinear318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalDerivedCoefficientMap318
open scoped TensorProduct
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Module R (NonreducedLineMayerVietoris318.H1 L) :=
  OriginalCoefficientCohomology318.cohomologyModule R (ContactRelativeStructuralHOne318.projection R c) L 1
local instance : Module S (NonreducedLineMayerVietoris318.H1 (pulled R S f c L)) :=
  OriginalCoefficientCohomology318.cohomologyModule S (ContactRelativeStructuralHOne318.projection S c)
    (pulled R S f c L) 1

lemma smul (r : R) (x : NonreducedLineMayerVietoris318.H1 L) :
    map R S f c L 1 (r • x) = f r • map R S f c L 1 x := by
  have ht : (1 : S) ⊗ₜ[R] (r • x) = f r ⊗ₜ[R] x := by
    rw [tmul_smul,smul_tmul']
    congr 1
    change algebraMap R S r * 1 = f r
    simp
  rw [← ContactCanonicalHOneBaseChange318.on_original,ht,
    ContactCanonicalHOneBaseChange318.pure_tensor]

/-- The map is still the independently defined Ext/unit pullback; only
its proved structural coefficient semilinearity is packaged here. -/
@[expose] def linear : NonreducedLineMayerVietoris318.H1 L →ₛₗ[f.toRingHom]
    NonreducedLineMayerVietoris318.H1 (pulled R S f c L) where
  __ := map R S f c L 1
  map_smul' := smul R S f c L
end ContactDerivedCoefficientSemilinear318
