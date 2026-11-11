module
public import OriginalLineAbelTransformation318
public import ContactNormalizedDivisorChartClass318
public import ContactNormalizedDivisorSection318
public section
noncomputable section
namespace ContactNormalizedAbelMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "q" => ContactRelativeStructuralHOne318.projection R c
local notation "B" => ContactNormalizedSectionParameter318.scheme R c L hz
local notation "b" => ContactNormalizedSectionParameter318.projection R c L hz
local notation "D" => ContactNormalizedGlobalIdealLine318.divisorLine R c L hz

/-- The actual normalized effective-Cartier family defines a genuine
Abel map from its parameter functor to the EXISTING relative fppf
line-class sheaf of the ORIGINAL contact model. Its input line is the
inverse of the actual global zero ideal, not a preassigned class. -/
@[expose] def transformation : yoneda.obj (Over.mk b) ⟶
    (RelativeFppfLineSheaf318.sheaf q).obj ⋙ forget CommGrpCat.{1} :=
  OriginalLineAbelTransformation318.transformation q b D

lemma on_test (T : Over (Spec R)) (a : T ⟶ Over.mk b) :
    (transformation R c L hz).app (op T) a=
      (RelativeFppfLineSheaf318.unit q).app (op T)
        (RelativeLineClassBaseChange318.testMap q b T.hom a.left a.w
          (RelativeLineClassQuotient318.classMap (pullback.snd q b) (classOf D))) := rfl
end ContactNormalizedAbelMap318
