module
public import RelativeLineAbelBaseTwist318
public import PELOriginalTranslationDifferenceFamily318
public import PELOriginalPolarizationTheoremOfSquare318
public section
noncomputable section
namespace PELOriginalRelativePolarizationTransformation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalTranslationDifferenceFamily318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The actual existing relative fppf line-class sheaf of the SAME
original proper smooth group scheme, not a representing dual scheme. -/
abbrev Target := RelativeFppfLineSheaf318.sheaf (π τ hτ)

/-- A genuine natural transformation on ALL scheme tests, including
nonreduced tests, from the actual original parameter scheme. Its family
is the whole algebraic m*L tensor inverse(pr1*L), not an analytic label. -/
@[expose] def transformation : yoneda.obj (Over.mk (π τ hτ)) ⟶
    (Target τ hτ).obj ⋙ forget CommGrpCat.{1} :=
  OriginalLineAbelTransformation318.transformation (π τ hτ) (π τ hτ) (family τ hτ)

lemma test_formula (T : Over (Spec (CommRingCat.of ℂ))) (a : T ⟶ Over.mk (π τ hτ)) :
    (transformation τ hτ).app (op T) a=
      (RelativeFppfLineSheaf318.unit (π τ hτ)).app (op T)
        (RelativeLineClassBaseChange318.testMap (π τ hτ) (π τ hτ) T.hom a.left a.w
          (RelativeLineClassQuotient318.classMap (second τ hτ) (classOf (family τ hτ)))) := rfl

/-- Contravariant naturality is the full scheme-test square, not only
invariance on algebraically closed points. -/
lemma naturality (T T' : Over (Spec (CommRingCat.of ℂ))) (f : T' ⟶ T)
    (a : T ⟶ Over.mk (π τ hτ)) :
    ((Target τ hτ).obj.map f.op) ((transformation τ hτ).app (op T) a)=
      (transformation τ hτ).app (op T') (f≫a) := by
  exact (congrFun ((transformation τ hτ).naturality f.op) a).symm

/-- Remove the parameter pullback factor by the ACTUAL relative line
quotient. This changes no value of the associated fppf transformation. -/
@[expose] def normalizedFamily : Line (Product τ hτ) :=
  RelativeLineAbelBaseTwist318.twist (π τ hτ) (π τ hτ) (family τ hτ)
    (FramedLineInverse318.inverse (line τ hτ))
lemma normalized_transformation :
    OriginalLineAbelTransformation318.transformation (π τ hτ) (π τ hτ) (normalizedFamily τ hτ)=
      transformation τ hτ :=
  RelativeLineAbelBaseTwist318.transformation_twist (π τ hτ) (π τ hτ) (family τ hτ)
    (FramedLineInverse318.inverse (line τ hτ))

/-- The unquotiented original complex fiber is still the SAME actual
translation-difference sheaf. This separate identity is not used to
assert injectivity after sheafification or all-test additivity. -/
@[expose] def originalFiberIso (q : PELOriginalPolarizationTransitions318.Base τ) :
    (LineSheafPullback318.line (slice τ hτ q) (family τ hτ)).object ≅
      (PELOriginalTranslationLineClass318.differenceLine τ hτ q).object :=
  fiberIso τ hτ q
end PELOriginalRelativePolarizationTransformation318
