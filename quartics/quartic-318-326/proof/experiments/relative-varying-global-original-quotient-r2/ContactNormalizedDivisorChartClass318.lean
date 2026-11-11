module
public import ContactNormalizedIdealChart318
public import LinePullbackInverseIso318
public section
noncomputable section
namespace ContactNormalizedDivisorChartClass318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
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
local notation "j" => ContactNormalizedAmbientCharts318.into R c L hz i
local notation "I" => ContactNormalizedGlobalIdealLine318.idealLine R c L hz
local notation "D" => ContactNormalizedGlobalIdealLine318.divisorLine R c L hz
local notation "N" => ContactNormalizedCartierTest318.line R c L hz i

/-- The divisor line of the SAME global normalized effective Cartier
family has the original line class on EVERY actual normalized coefficient
chart. This is genuine sheaf pullback and class equality, not a fiberwise
numerical comparison or a represented-Picard assumption. -/
lemma original_class : LineSheafPullback318.pullback j (classOf D)=classOf N := by
  rw [LinePullbackInverseIso318.class_inverse,
    ContactNormalizedIdealChart318.original_inverse_class,
    LineSheafClassGroup318.classOf_inverse,inv_inv]
end ContactNormalizedDivisorChartClass318
