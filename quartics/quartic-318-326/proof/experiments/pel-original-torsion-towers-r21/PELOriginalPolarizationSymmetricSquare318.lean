module
public import PELOriginalBalancedHyperplaneSquares318
public import PELOriginalPolarizationClassFaithful318
public section
noncomputable section
namespace PELOriginalPolarizationSymmetricSquare318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAlgebraicPolarizationLine318
open PELOriginalTranslationLineClass318 PELOriginalBalancedHyperplaneSquares318
variable (τ : ℂ) (hτ : 0 < τ.im)
lemma projection_neg (a : ComplexVectors) : projection (P τ) (-a)= -projection (P τ) a :=
  map_neg (QuotientAddGroup.mk' (P τ)) a

lemma cubic_class (q : Base τ) :
    action τ hτ q (classOf (cubicLine τ hτ))*action τ hτ (-q) (classOf (cubicLine τ hτ))=
      classOf (cubicLine τ hτ)^2 := by
  obtain ⟨a,rfl⟩ := quotient_surjective (P τ) q
  have he : classOf (LineSheafTensor318.line
    (LineSheafPullback318.line (PELOriginalTranslationFrameValues318.translate τ hτ a) (cubicLine τ hτ))
    (LineSheafPullback318.line (PELOriginalTranslationFrameValues318.translate τ hτ (-a)) (cubicLine τ hτ)))=
    classOf (LineSheafTensorPower318.line (cubicLine τ hτ) 2) :=
    classOf_eq (cubicSquareIso τ hτ a)
  rw [LineSheafClassGroup318.classOf_tensor,LineSheafTensorPower318.classOf_power] at he
  simpa only [PELOriginalTranslationFrameValues318.translate,
    projection_neg] using he

lemma quadratic_class (q : Base τ) :
    action τ hτ q (classOf (quadraticLine τ hτ))*action τ hτ (-q) (classOf (quadraticLine τ hτ))=
      classOf (quadraticLine τ hτ)^2 := by
  obtain ⟨a,rfl⟩ := quotient_surjective (P τ) q
  have he : classOf (LineSheafTensor318.line
    (LineSheafPullback318.line (PELOriginalTranslationFrameValues318.translate τ hτ a) (quadraticLine τ hτ))
    (LineSheafPullback318.line (PELOriginalTranslationFrameValues318.translate τ hτ (-a)) (quadraticLine τ hτ)))=
    classOf (LineSheafTensorPower318.line (quadraticLine τ hτ) 2) :=
    classOf_eq (quadraticSquareIso τ hτ a)
  rw [LineSheafClassGroup318.classOf_tensor,LineSheafTensorPower318.classOf_power] at he
  simpa only [PELOriginalTranslationFrameValues318.translate,
    projection_neg] using he

lemma degree_one_class : classOf (line τ hτ)=classOf (cubicLine τ hτ)*(classOf (quadraticLine τ hτ))⁻¹ :=
  PELOriginalPolarizationCube318.class_difference τ hτ

/-- Actual balanced-square relation for the SAME original degree-one
line. Both hyperplane square identities were constructed by regular
unit gauges, so their quotient is a relation of whole sheaf isomorphism. -/
theorem symmetric_class (q : Base τ) :
    action τ hτ q (classOf (line τ hτ))*action τ hτ (-q) (classOf (line τ hτ))=
      classOf (line τ hτ)^2 := by
  rw [degree_one_class,(action τ hτ q).map_mul,(action τ hτ q).map_inv,
    (action τ hτ (-q)).map_mul,(action τ hτ (-q)).map_inv]
  calc
    _ = (action τ hτ q (classOf (cubicLine τ hτ))*action τ hτ (-q) (classOf (cubicLine τ hτ)))*
        (action τ hτ q (classOf (quadraticLine τ hτ))*action τ hτ (-q) (classOf (quadraticLine τ hτ)))⁻¹ := by group
    _ = _ := by rw [cubic_class,quadratic_class]; group

/-- A genuine whole module-sheaf isomorphism, not only equality of
complex fiber dimensions or a formal relation in an abstract group. -/
@[expose] def symmetricIso (q : Base τ) :
    (LineSheafTensor318.line (translatedLine τ hτ q) (translatedLine τ hτ (-q))).object ≅
      (LineSheafTensorPower318.line (line τ hτ) 2).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [LineSheafClassGroup318.classOf_tensor,LineSheafTensorPower318.classOf_power]
  exact symmetric_class τ hτ q
end PELOriginalPolarizationSymmetricSquare318
