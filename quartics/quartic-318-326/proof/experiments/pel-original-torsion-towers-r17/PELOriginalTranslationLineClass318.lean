module
public import LineClassPullbackGroup318
public import PELOriginalPolarizationCube318
public import PELOriginalTranslationAutomorphisms318
public section
noncomputable section
namespace PELOriginalTranslationLineClass318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalPolarizationTransitions318
open PELOriginalTranslationAutomorphisms318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Pullback by the genuine scheme translation, on actual line classes. -/
@[expose] def action (q : Base τ) : Class (candidate τ hτ) →* Class (candidate τ hτ) :=
  LineClassPullbackGroup318.hom (translation τ hτ q)
lemma action_zero (c : Class (candidate τ hτ)) : action τ hτ 0 c=c := by
  change LineSheafPullback318.pullback (translation τ hτ 0) c=c
  rw [translation_zero,LineClassPullbackLaws318.pullback_identity]
lemma action_add (q r : Base τ) (c : Class (candidate τ hτ)) :
    action τ hτ (q+r) c=action τ hτ q (action τ hτ r c) := by
  change LineSheafPullback318.pullback (translation τ hτ (q+r)) c=_
  rw [←translation_comp,LineClassPullbackLaws318.pullback_composition]
  rfl

@[expose] def translatedLine (q : Base τ) : Line (candidate τ hτ) :=
  LineSheafPullback318.line (translation τ hτ q)
    (PELOriginalAlgebraicPolarizationLine318.line τ hτ)
/-- The actual translated tensor difference t_q^*L tensor L^{-1}.
No represented Picard or algebraic dual scheme is postulated here. -/
@[expose] def differenceLine (q : Base τ) : Line (candidate τ hτ) :=
  LineSheafTensor318.line (translatedLine τ hτ q)
    (FramedLineInverse318.inverse (PELOriginalAlgebraicPolarizationLine318.line τ hτ))
@[expose] def polarizationClass (q : Base τ) : Class (candidate τ hτ) :=
  classOf (differenceLine τ hτ q)
lemma class_formula (q : Base τ) : polarizationClass τ hτ q=
    action τ hτ q (classOf (PELOriginalAlgebraicPolarizationLine318.line τ hτ)) *
      (classOf (PELOriginalAlgebraicPolarizationLine318.line τ hτ))⁻¹ := by
  rw [polarizationClass,differenceLine,LineSheafClassGroup318.classOf_tensor,
    LineSheafClassGroup318.classOf_inverse]
  rfl
lemma zero_class : polarizationClass τ hτ 0=1 := by
  rw [class_formula,action_zero,mul_inv_cancel]

/-- The actual universal coboundary identity. This is a TWISTED cocycle;
untwisting it requires the theorem of square, not merely group notation. -/
lemma twisted_add (q r : Base τ) : polarizationClass τ hτ (q+r)=
    action τ hτ q (polarizationClass τ hτ r) * polarizationClass τ hτ q := by
  rw [class_formula,class_formula,class_formula,(action τ hτ q).map_mul,
    (action τ hτ q).map_inv,action_add]
  group
end PELOriginalTranslationLineClass318
