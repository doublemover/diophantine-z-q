module
public import PELOriginalOrderedCharacterCoordinate318
public import PELOriginalCommonLegendreBase318
public section
noncomputable section
namespace PELOriginalCharacterAlgebraicRelabeling318
open AlgebraicGeometry CategoryTheory
open PELOriginalMaximalQuotient318
open ProjectiveLineComplexSchemePoints318 ProjectiveLineAlgebraicNormalization318
open ProjectiveLineFourPointAlgebraicNormalization318

/-- The manuscript normalization followed by the explicitly ordered
character normalization, as an actual algebraic Proj isomorphism. -/
@[expose] def realization (i:Fin 4) := compose
  PELOriginalManuscriptNormalization318.algebraic
  (fourPoints (PELOriginalOrderedCharacterCoordinate318.points i)
    (PELOriginalOrderedCharacterCoordinate318.points_injective i))

@[expose] def point (i:Fin 4) (q:MaximalBase) : SchemePoints:=
  pointMap (realization i).schemeIso.hom (realization i).over_base
    (PELOriginalFourBranchAlgebraicTarget318.originalPoint q)
lemma point_exact (i:Fin 4) (q:MaximalBase) : point i q=
    spherePoint (PELOriginalOrderedCharacterCoordinate318.coordinate i q) := by
  apply Subtype.ext
  exact (realization i).action (PELOriginalFourBranchCoordinate318.originalSphere q)

/-- Full algebraic target change from the original arbitrary branch order
to the new explicit manuscript order. The source cover is not changed. -/
@[expose] def targetIso (i:Fin 4) :
    ProjectiveJLine318.scheme ℂ≅ProjectiveJLine318.scheme ℂ:=
  (PELOriginalFourBranchAlgebraicTarget318.realization i).schemeIso.symm.trans
    (realization i).schemeIso
lemma target_over_base (i:Fin 4) :
    (targetIso i).hom≫ProjectiveJLine318.structureMap ℂ=ProjectiveJLine318.structureMap ℂ := by
  change ((PELOriginalFourBranchAlgebraicTarget318.realization i).schemeIso.inv≫
    (realization i).schemeIso.hom)≫_=_
  rw [Category.assoc,(realization i).over_base]
  exact inverse_over_base _ (PELOriginalFourBranchAlgebraicTarget318.realization i).over_base

/-- Equality of the FULL original Spec-C-valued morphisms at the actual
consumer, not agreement of coordinates or cardinalities only. -/
theorem actual_relabeling (i:Fin 4) (q:MaximalBase) :
    (PELOriginalFourBranchAlgebraicTarget318.normalizedPoint i q).val≫(targetIso i).hom=
      (point i q).val := by
  change ((PELOriginalFourBranchAlgebraicTarget318.originalPoint q).val≫
    (PELOriginalFourBranchAlgebraicTarget318.realization i).schemeIso.hom)≫
    ((PELOriginalFourBranchAlgebraicTarget318.realization i).schemeIso.inv≫
      (realization i).schemeIso.hom)=_
  rw [Category.assoc,←Category.assoc
      (PELOriginalFourBranchAlgebraicTarget318.realization i).schemeIso.hom,
    (PELOriginalFourBranchAlgebraicTarget318.realization i).schemeIso.hom_inv_id,
    Category.id_comp]
  rfl

/-- The SAME actual original character projection lands in the relabeled
base by composition with the actual algebraic target isomorphism. -/
theorem original_projection_relabeling (i:Fin 4)
    (x:PELOriginalCharacterQuotient318.CharacterBase i) :
    (PELOriginalCommonLegendreBase318.originalProjection i x).val≫(targetIso i).hom=
      (spherePoint (PELOriginalOrderedCharacterCoordinate318.normalizedMap i x)).val := by
  rw [←point_exact i (PELOriginalCharacterQuotient318.toMaximal i x)]
  exact actual_relabeling i (PELOriginalCharacterQuotient318.toMaximal i x)
end PELOriginalCharacterAlgebraicRelabeling318
