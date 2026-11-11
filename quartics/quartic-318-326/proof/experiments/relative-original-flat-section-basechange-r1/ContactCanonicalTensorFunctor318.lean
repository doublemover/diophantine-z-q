module
public import ContactDerivedCoefficientSemilinear318
public import OriginalCoefficientCohomologyMaps318
public section
noncomputable section
namespace ContactCanonicalTensorFunctor318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalDerivedCoefficientMap318
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S T : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S] [Algebra ℚ T]
  (f : R →ₐ[ℚ] S) (g : S →ₐ[ℚ] T) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Algebra S T := g.toAlgebra
local instance : Algebra R T := (g.comp f).toAlgebra
local instance : Module R (NonreducedLineMayerVietoris318.H1 L) :=
  OriginalCoefficientCohomology318.cohomologyModule R (ContactRelativeStructuralHOne318.projection R c) L 1
local instance : Module S (NonreducedLineMayerVietoris318.H1 (pulled R S f c L)) :=
  OriginalCoefficientCohomology318.cohomologyModule S (ContactRelativeStructuralHOne318.projection S c) _ 1
local instance (N : Line (curve T c)) : Module T (NonreducedLineMayerVietoris318.H1 N) :=
  OriginalCoefficientCohomology318.cohomologyModule T (ContactRelativeStructuralHOne318.projection T c) N 1

/-- The exact iterated scalar-extension composition formula on arbitrary
pure-tensor generators, retaining t*g(s), the original line associator,
and the genuine original derived maps. -/
lemma composition (t : T) (s : S) (x : NonreducedLineMayerVietoris318.H1 L) :
    Sheaf.H.map ((SheafOfModules.toSheaf (curve T c).ringCatSheaf).map
      (ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom) 1
      (ContactOriginalHOneBaseChange318.equivalence S T g c (pulled R S f c L)
        (t ⊗ₜ[S] ContactOriginalHOneBaseChange318.equivalence R S f c L (s ⊗ₜ[R] x))) =
    ContactOriginalHOneBaseChange318.equivalence R T (g.comp f) c L ((t * g s) ⊗ₜ[R] x) := by
  let a := OriginalCoefficientCohomologyMaps318.map T (ContactRelativeStructuralHOne318.projection T c)
    (pulled S T g c (pulled R S f c L)) (pulled R T (g.comp f) c L)
    (ContactDerivedCoefficientFunctor318.compositionIso R S T f g c L).hom 1
  change a _ = _
  rw [ContactCanonicalHOneBaseChange318.pure_tensor,
    ContactCanonicalHOneBaseChange318.pure_tensor,
    ContactDerivedCoefficientSemilinear318.smul,map_smul,map_smul,
    ContactCanonicalHOneBaseChange318.pure_tensor]
  change t • (g s • Sheaf.H.map _ 1
    (map S T g c (pulled R S f c L) 1 (map R S f c L 1 x))) = _
  rw [ContactDerivedCoefficientFunctor318.composition,mul_smul]

variable (N : Line (curve R c))
local instance : Module R (NonreducedLineMayerVietoris318.H1 N) :=
  OriginalCoefficientCohomology318.cohomologyModule R (ContactRelativeStructuralHOne318.projection R c) N 1
local instance : Module R (NonreducedLineMayerVietoris318.H1 (pulled R R (AlgHom.id ℚ R) c N)) :=
  OriginalCoefficientCohomology318.cohomologyModule R (ContactRelativeStructuralHOne318.projection R c) _ 1

lemma identity (r : R) (x : NonreducedLineMayerVietoris318.H1 N) :
    Sheaf.H.map ((SheafOfModules.toSheaf (curve R c).ringCatSheaf).map
      (ContactDerivedCoefficientFunctor318.identityIso R c N).hom) 1
      (ContactOriginalHOneBaseChange318.equivalence R R (AlgHom.id ℚ R) c N (r ⊗ₜ[R] x)) = r • x := by
  let a := OriginalCoefficientCohomologyMaps318.map R (ContactRelativeStructuralHOne318.projection R c)
    (pulled R R (AlgHom.id ℚ R) c N) N (ContactDerivedCoefficientFunctor318.identityIso R c N).hom 1
  change a _ = _
  rw [ContactCanonicalHOneBaseChange318.pure_tensor,map_smul]
  exact congrArg (fun y => r • y) (ContactDerivedCoefficientFunctor318.identity R c N x)
end ContactCanonicalTensorFunctor318
