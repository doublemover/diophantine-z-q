module
public import ContactZeroIntersectionLegs318
public section
noncomputable section
namespace ContactZeroTripleLeg318
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
local notation "P" => Γ(L.object,⊤)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "inc" => ContactNormalizedZeroTransitions318.inclusion R c L hz
local notation "trans" => ContactNormalizedZeroTransitions318.transition R c L hz
local notation "triple" => ContactZeroTripleTransition318.transition R c L hz
variable (i j k : Fin F.size)

/-- The actual triple transition restricts to the actual pairwise zero
transition on the correct overlap leg. Joint monicity requires BOTH the
original curve map and the literal base-overlap projection, each checked
using its genuine geometric comparison. -/
lemma leg : triple i j k ≫ pullback.snd (inc j k) (inc j i)=
    pullback.fst (inc i j) (inc i k) ≫ (trans i j).hom := by
  apply ContactZeroOverlapJointMono318.hom_ext R c L hz j i
  · simp only [ContactZeroTripleTransition318.transition,Category.assoc]
    rw [ContactZeroIntersectionLegs318.inverse_original_second,
      ContactLiteralTripleFamilyCycle318.rotation_original,
      ContactZeroIntersectionLegs318.original,
      ContactZeroOverlapOriginal318.transition]
  · simp only [ContactZeroTripleTransition318.transition,Category.assoc]
    rw [ContactZeroIntersectionLegs318.inverse_second,
      ContactLiteralTripleFamilyRotation318.rotation_projection_assoc,
      ProjectiveParameterSliceTripleSchemes318.leg,
      ContactZeroIntersectionLegs318.first_leg_assoc,
      ContactNormalizedZeroTransitions318.transition_projection]
end ContactZeroTripleLeg318
