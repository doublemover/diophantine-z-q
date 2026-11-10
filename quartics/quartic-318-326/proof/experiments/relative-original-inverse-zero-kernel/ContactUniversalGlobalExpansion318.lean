module
public import UniversalScalarCoordinate318
public import ContactHZeroGeometricUnit318
public import ContactOriginalSectionParameter318
public section
noncomputable section
namespace ContactUniversalGlobalExpansion318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactOriginalSectionParameter318
open scoped TensorProduct BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "P" => Γ(L.object,⊤)
local notation "S" => CommRingCat.of (parameterRing R c L)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local instance : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' rfl
local instance : Module S Γ((universalLine R c L).object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c)
    (universalLine R c L) ⊤

/-- The actual original GLOBAL universal section is the explicit finite
sum of the original geometric pullbacks with its genuine symmetric
coordinate coefficients. This pins the object before any local frame. -/
lemma global_sum : universalSection R c L hz = ∑ i,
    SymmetricAlgebra.ι R (Module.Dual R P) (F.coordinate i) •
      OriginalSectionPullbackComposition318.pull
        (ContactRelativeCoefficientChange318.curveMap R S (parameterCoefficient R c L) c)
        L.object (F.vector i) := by
  change ContactRelativeHZeroBaseChange318.equivalence R S (parameterCoefficient R c L) c L hz
    (ProjectiveSectionParameter318.universal R P)=_
  rw [UniversalScalarCoordinate318.universal_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact ContactHZeroGeometricUnit318.pure_tensor R c L S (parameterCoefficient R c L) hz _ _

local instance : Module S (finiteSections S c (universalLine R c L)) :=
  finiteModule S c (universalLine R c L)
local instance : Module S (infinitySections S c (universalLine R c L)) :=
  infinityModule S c (universalLine R c L)

/-- Actual finite-chart section, before choosing any frame, with its
original geometric coefficient restriction and every coefficient retained. -/
lemma finite_sum : (ContactRelativeOriginalHZero318.pair S c (universalLine R c L)
    (universalSection R c L hz)).1 = ∑ i,
    SymmetricAlgebra.ι R (Module.Dual R P) (F.coordinate i) •
      ContactCoefficientLineCharts318.finiteRestriction R S (parameterCoefficient R c L) c L
        (ContactRelativeOriginalHZero318.pair R c L (F.vector i)).1 := by
  change ((LinearMap.fst S _ _).comp
    (ContactRelativeOriginalHZero318.pair S c (universalLine R c L)))
      (universalSection R c L hz)=_
  rw [global_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  change _ • (ContactRelativeOriginalHZero318.pair S c (universalLine R c L) _).1 = _
  rw [ContactHZeroGeometricUnit318.geometric_coordinates]

/-- The actual infinity route has its OWN original restriction; the
finite chart frame is not substituted across the reciprocal overlap. -/
lemma infinity_sum : (ContactRelativeOriginalHZero318.pair S c (universalLine R c L)
    (universalSection R c L hz)).2 = ∑ i,
    SymmetricAlgebra.ι R (Module.Dual R P) (F.coordinate i) •
      ContactCoefficientLineCharts318.infinityRestriction R S (parameterCoefficient R c L) c L
        (ContactRelativeOriginalHZero318.pair R c L (F.vector i)).2 := by
  change ((LinearMap.snd S _ _).comp
    (ContactRelativeOriginalHZero318.pair S c (universalLine R c L)))
      (universalSection R c L hz)=_
  rw [global_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  change _ • (ContactRelativeOriginalHZero318.pair S c (universalLine R c L) _).2 = _
  rw [ContactHZeroGeometricUnit318.geometric_coordinates]
end ContactUniversalGlobalExpansion318
