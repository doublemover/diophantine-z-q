module
public import ContactNormalizedDivisorChartClass318
public import CartesianRelativeClassComparison318
public section
noncomputable section
namespace ContactNormalizedOriginalClass318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R Γ(L.object,⊤)
variable (i : Fin F.size)
local notation "A" => CommRingCat.of (parameterRing R c L)
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
local notation "S" => ContactNormalizedCartierTest318.ring R c L hz i
local notation "g" => ContactNormalizedCartierTest318.coefficient R c L hz i
local notation "f" => parameterCoefficient R c L
local notation "a" => ContactRelativeCoefficientChange318.curveMap R S (g.comp f) c
local notation "j" => ContactNormalizedAmbientCharts318.into R c L hz i
local notation "D" => ContactNormalizedGlobalIdealLine318.divisorLine R c L hz
local notation "p" => ContactRelativeStructuralHOne318.projection R c
local notation "b" => ContactNormalizedSectionParameter318.projection R c L hz
local notation "u" => ProjectiveParameterSliceGluing318.into R Γ(L.object,⊤) i

/-- On every actual normalized coefficient chart, the divisor line is
exactly the pullback of the ORIGINAL line, through both actual coefficient
changes. This identifies what the fixed-line Abel family really varies. -/
lemma original_class : LineClassPullbackHom318.pullback j (classOf D)=
    LineClassPullbackHom318.pullback a (classOf L) := by
  change LineSheafPullback318.pullback j (classOf D)=_
  rw [ContactNormalizedDivisorChartClass318.original_class]
  change LineClassPullbackHom318.pullback (ContactRelativeCoefficientChange318.curveMap A S g c)
    (LineClassPullbackHom318.pullback (ContactRelativeCoefficientChange318.curveMap R A f c)
      (classOf L))=LineClassPullbackHom318.pullback a (classOf L)
  rw [← MonoidHom.comp_apply,← LineClassPullbackHom318.composition,
    ContactCoefficientWholeOpens318.composition]

/-- The same equality is consumed at the ACTUAL naive relative-class
test map, after transporting the specified contact chart to its genuine
standard Cartesian fiber product. Not merely equality on field points. -/
lemma relative_chart : RelativeLineClassBaseChange318.testMap p b (u ≫ b) u rfl
    (RelativeLineClassQuotient318.classMap (pullback.snd p b) (classOf D))=
    RelativeLineClassQuotient318.classMap (pullback.snd p (u ≫ b))
      (LineClassPullbackHom318.pullback (pullback.fst p (u ≫ b)) (classOf L)) :=
  CartesianRelativeClassComparison318.relative_on_test p b u a
    (ContactRelativeStructuralHOne318.projection S c)
    (ContactNormalizedAmbientCharts318.coefficient_square R c L hz i)
    (classOf D) (classOf L) (original_class R c L hz i)
end ContactNormalizedOriginalClass318
