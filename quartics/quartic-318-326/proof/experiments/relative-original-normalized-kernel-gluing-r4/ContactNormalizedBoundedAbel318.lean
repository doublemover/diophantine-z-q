module
public import ContactNormalizedBoundedDivisor318
public import ContactNormalizedAbelTransformationFiber318
public section
noncomputable section
namespace ContactNormalizedBoundedAbel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "p" => ContactRelativeStructuralHOne318.projection R c
local notation "b" => ContactNormalizedSectionParameter318.projection R c L hz
/-- Abel transformation of the actual bounded-classified family, viewed
on the SAME original relative curve through its exact ambient comparison. -/
@[expose] def transformation : yoneda.obj (Over.mk b) ⟶
    (RelativeFppfLineSheaf318.sheaf p).obj ⋙ forget CommGrpCat.{1} :=
  OriginalLineAbelTransformation318.transformation p b (ContactNormalizedBoundedDivisor318.line R c L hz)
lemma original_transformation : transformation R c L hz=ContactNormalizedAbelMap318.transformation R c L hz :=
  OriginalLineAbelTransformation318.class_congr p b _ _ (ContactNormalizedBoundedDivisor318.original_class R c L hz)
/-- The new represented bounded varying-divisor parameter now receives
the old fixed-line section family with the correct actual Abel fiber on
ALL scheme tests. No represented Picard quotient is silently inferred. -/
lemma fixed_line : transformation R c L hz=OriginalLineAbelTransformation318.transformation p b
    (LineSheafPullback318.line (pullback.fst p b) L) :=
  (original_transformation R c L hz).trans
    (ContactNormalizedAbelTransformationFiber318.original_transformation R c L hz)
lemma original_value : RelativeClassSheafPoint318.value p b
    (OriginalLineAbelTransformation318.point p b (ContactNormalizedBoundedDivisor318.line R c L hz))=
    RelativeClassSheafPoint318.value p b (RelativeClassSheafPoint318.original p b (classOf L)) := by
  have he := congrArg (fun x => RelativeLineClassQuotient318.classMap (pullback.snd p b) x)
    (ContactNormalizedBoundedDivisor318.original_class R c L hz)
  change OriginalLineAbelTransformation318.point p b (ContactNormalizedBoundedDivisor318.line R c L hz)=
    OriginalLineAbelTransformation318.point p b (ContactNormalizedGlobalIdealLine318.divisorLine R c L hz) at he
  rw [he]
  exact ContactNormalizedAbelFiber318.original_sheaf_class R c L hz
end ContactNormalizedBoundedAbel318
