module
public import ContactRelativeFiniteProjectiveHZero318
public import PolynomialProjectiveJet318
public section
noncomputable section
namespace ContactRelativeInfinityJet318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : IsScalarTower ℚ (Polynomial ℚ) (infinityRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : IsScalarTower R (Polynomial R) (infinitySections R c L) := IsScalarTower.of_compHom ..
local instance : Module.Projective (Polynomial R) (infinitySections R c L) :=
  RelativePolynomialChartProjective318.sections_projective R (infinityRing c) (infinityLine R c L)

/-- Literal multiplication by u^(b+1) on the WHOLE original infinity
line module, not a selected finite jet vector space. -/
@[expose] def power (b : ℕ) := PolynomialProjectiveJet318.power R (infinitySections R c L) b

lemma injective (b : ℕ) : Function.Injective (power R c L b) :=
  PolynomialProjectiveJet318.power_injective R (infinitySections R c L) b

/-- The actual infinity quotient by the original coordinate power is
finite projective over every coefficient ring. -/
theorem finite_projective (b : ℕ) :
    Module.Finite R (infinitySections R c L ⧸ (power R c L b).range) ∧
    Module.Projective R (infinitySections R c L ⧸ (power R c L b).range) :=
  PolynomialProjectiveJet318.finite_projective R (infinitySections R c L) b
end ContactRelativeInfinityJet318
