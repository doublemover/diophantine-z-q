module
public import OriginalCoefficientTensorSection318
public import OriginalAffineUniversalParameterSection318
public import ContactUniversalGlobalExpansion318
public import ContactPositiveChartEvaluation318
public section
noncomputable section
namespace ContactUniversalChartRelabel318
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
local instance : Algebra ℚ S := ((algebraMap R S).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq' rfl

@[expose] def finitePath : (Scheme.Modules.pullback
    (Spec.map (ContactRelativeCoefficientChange318.finiteRingMap R S (parameterCoefficient R c L) c))).obj
      (finiteLine R c L).object ≅ (finiteLine S c (universalLine R c L)).object :=
  OriginalCoefficientChartLine318.sheafComparison
    (ContactRelativeCoefficientChange318.curveMap R S (parameterCoefficient R c L) c)
    (ContactRelativeCoefficientChange318.finiteRingMap R S (parameterCoefficient R c L) c)
    (finiteInto R c) (finiteInto S c)
    (ContactRelativeCoefficientChange318.finite_square R S (parameterCoefficient R c L) c) L

@[expose] def infinityPath : (Scheme.Modules.pullback
    (Spec.map (ContactRelativeCoefficientChange318.infinityRingMap R S (parameterCoefficient R c L) c))).obj
      (infinityLine R c L).object ≅ (infinityLine S c (universalLine R c L)).object :=
  OriginalCoefficientChartLine318.sheafComparison
    (ContactRelativeCoefficientChange318.curveMap R S (parameterCoefficient R c L) c)
    (ContactRelativeCoefficientChange318.infinityRingMap R S (parameterCoefficient R c L) c)
    (infinityInto R c) (infinityInto S c)
    (ContactRelativeCoefficientChange318.infinity_square R S (parameterCoefficient R c L) c) L

abbrev finiteTensorSection := OriginalAffineUniversalParameterSection318.section R
  (CommRingCat.of (R ⊗[ℚ] finiteRing c)) (finiteLine R c L) P
  (ContactPositiveChartEvaluation318.finiteRestriction R c L)
abbrev infinityTensorSection := OriginalAffineUniversalParameterSection318.section R
  (CommRingCat.of (R ⊗[ℚ] infinityRing c)) (infinityLine R c L) P
  (ContactPositiveChartEvaluation318.infinityRestriction R c L)

/-- The actual canonical chart tensor cancellation carries the explicit
affine universal section to the literal finite restriction of the SAME
original GLOBAL universal section. Not a matching function-field section. -/
lemma finite_section : OriginalCoefficientTensorSection318.restriction (CommRingCat.of ℚ)
    R S (CommRingCat.of (finiteRing c)) (parameterCoefficient R c L)
    (finiteLine R c L) (finiteLine S c (universalLine R c L)) (finitePath R c L)
      (finiteTensorSection R c L hz) =
    (ContactRelativeOriginalHZero318.pair S c (universalLine R c L) (universalSection R c L hz)).1 := by
  rw [finiteTensorSection,OriginalAffineUniversalParameterSection318.section,
    OriginalCoefficientTensorSection318.expansion]
  have hs := congrArg (finiteIdentity S c (universalLine R c L))
    (ContactUniversalGlobalExpansion318.finite_sum R c L hz)
  rw [map_sum] at hs
  simp only [map_smul] at hs
  exact hs.symm

/-- Independently retain the original infinity chart and its canonical
cancellation map; no finite-chart comparison is reused at infinity. -/
lemma infinity_section : OriginalCoefficientTensorSection318.restriction (CommRingCat.of ℚ)
    R S (CommRingCat.of (infinityRing c)) (parameterCoefficient R c L)
    (infinityLine R c L) (infinityLine S c (universalLine R c L)) (infinityPath R c L)
      (infinityTensorSection R c L hz) =
    (ContactRelativeOriginalHZero318.pair S c (universalLine R c L) (universalSection R c L hz)).2 := by
  rw [infinityTensorSection,OriginalAffineUniversalParameterSection318.section,
    OriginalCoefficientTensorSection318.expansion]
  have hs := congrArg (infinityIdentity S c (universalLine R c L))
    (ContactUniversalGlobalExpansion318.infinity_sum R c L hz)
  rw [map_sum] at hs
  simp only [map_smul] at hs
  exact hs.symm
end ContactUniversalChartRelabel318
