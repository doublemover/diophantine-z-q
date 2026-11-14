module
public import PELOriginalOrderedCharacterPointMap318
public import FourRootProjectivePointComparison318
public section
noncomputable section
namespace PELOriginalOrderedPointProjection318
open AlgebraicGeometry CategoryTheory
open PELOriginalCharacterQuotient318 PELOriginalOrderedCharacterPointMap318
open PELOriginalOrderedCharacterCoordinate318 PELOriginalNormalizedBaseSchemeSquare318
open PELOriginalOrderedBaseSchemeNormalization318
open NormalizedLegendreFiniteProjection318 ProjectiveLineComplexSchemePoints318

/-- The descended point is on the EXACT normalized original base, at
every character point, including all branches and infinity. -/
theorem projection_square (i:Fin 4) (x:CharacterBase i):
    project (parameter i) (pointMap i x)=spherePoint (normalizedMap i x):=by
  refine Quotient.inductionOn x ?_
  intro a
  apply Subtype.ext
  change ((PELOriginalContactSchemePoints318.comparison a).val≫
    PELOriginalWholeCharacterMorphisms318.morphism i)≫
      NormalizedLegendreSchemeProjection318.projection (parameter i)=_
  rw [Category.assoc,whole_square,←Category.assoc]
  have h:=congrArg Subtype.val (FourRootProjectivePointComparison318.original_projection a)
  change (PELOriginalContactSchemePoints318.comparison a).val≫
    FourRootProjectiveProjection318.projection PELOriginalCommonContactBase318.branches=_ at h
  rw [h]
  exact original_coordinate_square i (PELOriginalMaximalQuotient318.projection a)

lemma normalized_surjective (i:Fin 4):Function.Surjective (normalizedMap i):=
  (coordinate i).surjective.comp (PELOriginalCharacterTopology318.toMaximal_surjective i)

/-- Equality of image points implies equality of the SAME original
maximal-base point. This is stronger than an unrelated fiber count. -/
lemma same_base (i:Fin 4) {x y:CharacterBase i} (h:pointMap i x=pointMap i y):
    toMaximal i x=toMaximal i y:=by
  have hp:=congrArg (project (parameter i)) h
  rw [projection_square,projection_square] at hp
  exact (coordinate i).injective (spherePoint_bijective.1 hp)
end PELOriginalOrderedPointProjection318
