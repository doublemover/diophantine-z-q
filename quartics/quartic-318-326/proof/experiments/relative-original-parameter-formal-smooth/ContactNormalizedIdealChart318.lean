module
public import ActualOpenIdealKernelIso318
public import ContactNormalizedGlobalIdealLine318
public import ContactNormalizedTestIdealLine318
public import ContactNormalizedZeroCartierSquare318
public import LineSheafPullback318
public section
noncomputable section
namespace ContactNormalizedIdealChart318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
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
local notation "p" => ContactNormalizedGlobalClosedFamily318.into R c L hz
local notation "q" => ContactNormalizedCartierTest318.into R c L hz i
local notation "j" => ContactNormalizedAmbientCharts318.into R c L hz i
local notation "k" => ContactNormalizedZeroCartierSquare318.into R c L hz i
local notation "I" => ContactNormalizedGlobalIdealLine318.idealLine R c L hz
local notation "N" => ContactNormalizedCartierTest318.line R c L hz i

/-- The GENUINE pullback of the original global invertible ideal is the
inverse of the SAME original pulled line on every actual normalized
coefficient chart. The comparison uses the full Cartesian zero square,
actual kernel restriction and exact original inverse-line contraction. -/
@[expose] def iso : (LineSheafPullback318.line j I).object ≅
    (FramedLineInverse318.inverse N).object :=
  (Scheme.Modules.pullback j).mapIso
    (eqToIso (ContactNormalizedGlobalIdealLine318.idealLine_object R c L hz)) ≪≫
  ((Scheme.Modules.restrictFunctorIsoPullback j).app
    (ActualClosedIdealModule318.object p)).symm ≪≫
  ActualOpenIdealKernelIso318.iso p q k j (ContactNormalizedZeroCartierSquare318.square R c L hz i) ≪≫
  (ContactNormalizedTestIdealLine318.iso R c L hz i).symm

lemma original_inverse_class :
    LineSheafPullback318.pullback j (classOf I)=classOf (FramedLineInverse318.inverse N) :=
  LineSheafClass318.classOf_eq (iso R c L hz i)
end ContactNormalizedIdealChart318
