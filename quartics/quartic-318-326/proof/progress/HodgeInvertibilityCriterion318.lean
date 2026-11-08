module
public import IntrinsicHodgeComparison318
public import StructurePushforwardSplit318
public section
noncomputable section
namespace HodgeInvertibilityCriterion318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

section CategoryEvaluation
variable {C D : Type u} [Category C] [Category D]
  {F : C ⥤ D} {G H : D ⥤ C}

/-- Evaluation is invertible on an object descended from the base whenever the
actual adjunction unit at that base object is invertible. -/
theorem evaluation_isIso (adj : F ⊣ G) (α : F ⋙ H ≅ 𝟭 C) (N : C)
    [IsIso (adj.unit.app N)] :
    IsIso ((IntrinsicHodgeComparison318.evaluation adj α).app (F.obj N)) := by
  haveI : IsIso (adj.unit.app N ≫
      (IntrinsicHodgeComparison318.evaluation adj α).app (F.obj N)) := by
    rw [IntrinsicHodgeComparison318.unit_evaluation]
    infer_instance
  exact IsIso.of_isIso_comp_left (adj.unit.app N) _

/-- Evaluation invertibility transports along an actual isomorphism of source
objects, using the naturality square rather than a chosen comparison map. -/
theorem evaluation_isIso_of_iso (adj : F ⊣ G) (α : F ⋙ H ≅ 𝟭 C)
    {M N : D} (e : M ≅ N)
    [IsIso ((IntrinsicHodgeComparison318.evaluation adj α).app N)] :
    IsIso ((IntrinsicHodgeComparison318.evaluation adj α).app M) := by
  have h := (IntrinsicHodgeComparison318.evaluation adj α).naturality e.hom
  haveI : IsIso ((IntrinsicHodgeComparison318.evaluation adj α).app M ≫ H.map e.hom) := by
    rw [←h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (H.map e.hom)
end CategoryEvaluation

variable {X S : Scheme.{u}} (p : X ⟶ S) (e : S ⟶ X) (he : e ≫ p=𝟙 S)

/-- The actual pullback/pushforward unit on O becomes the actual structure-sheaf
map after the canonical pullback-of-O isomorphism. -/
theorem adjunction_unit_structure :
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
        (SheafOfModules.unit S.ringCatSheaf) ≫
      (Scheme.Modules.pushforward p).map (IdentityCotangent318.pullbackUnitIso p).hom =
        StructurePushforwardSplit318.unitMap p := by
  letI : (SheafOfModules.pushforward.{u} p.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward p).IsRightAdjoint
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    p.toRingCatSheafHom

/-- If actual regular functions descend, canonical evaluation on O is invertible. -/
theorem unit_evaluation_isIso [IsIso (StructurePushforwardSplit318.unitMap p)] :
    IsIso (IntrinsicHodgeComparison318.evaluateAtSection p e he
      (SheafOfModules.unit X.ringCatSheaf)) := by
  haveI : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
      (SheafOfModules.unit S.ringCatSheaf) ≫
    (Scheme.Modules.pushforward p).map (IdentityCotangent318.pullbackUnitIso p).hom) := by
    rw [adjunction_unit_structure]
    infer_instance
  haveI : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
      (SheafOfModules.unit S.ringCatSheaf)) :=
    IsIso.of_isIso_comp_right _
      ((Scheme.Modules.pushforward p).map (IdentityCotangent318.pullbackUnitIso p).hom)
  haveI := evaluation_isIso (Scheme.Modules.pullbackPushforwardAdjunction p)
    (IntrinsicHodgeComparison318.sectionPullbackIso p e he) (SheafOfModules.unit S.ringCatSheaf)
  exact evaluation_isIso_of_iso (Scheme.Modules.pullbackPushforwardAdjunction p)
    (IntrinsicHodgeComparison318.sectionPullbackIso p e he)
    (IdentityCotangent318.pullbackUnitIso p).symm

/-- The two remaining geometric inputs are isolated exactly: descent of actual
regular functions and an actual intrinsic differential frame. -/
theorem evaluation_isIso_of_frame [IsIso (StructurePushforwardSplit318.unitMap p)]
    {M : X.Modules} (frame : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (IntrinsicHodgeComparison318.evaluateAtSection p e he M) := by
  haveI : IsIso ((IntrinsicHodgeComparison318.evaluation
      (Scheme.Modules.pullbackPushforwardAdjunction p)
      (IntrinsicHodgeComparison318.sectionPullbackIso p e he)).app
        (SheafOfModules.unit X.ringCatSheaf)) := unit_evaluation_isIso p e he
  exact evaluation_isIso_of_iso (Scheme.Modules.pullbackPushforwardAdjunction p)
    (IntrinsicHodgeComparison318.sectionPullbackIso p e he) frame

variable {R : Type u} [CommRing R] (A B : R)

/-- A precise conditional criterion for the actual canonical Hodge map. The
frame and regular-function descent are explicit, not assumed invisibly. -/
theorem hodgeToIdentity_isIso
    [IsIso (StructurePushforwardSplit318.unitMap (WeierstrassGluing318.structureMap A B))]
    (frame : FamilyIntrinsicDifferentials318.familyOmega A B ≅ GlobalInvariantLine318.line A B) :
    IsIso (IntrinsicHodgeComparison318.hodgeToIdentity A B) :=
  evaluation_isIso_of_frame _ _ (WeierstrassGluing318.infinity_section A B) frame
end HodgeInvertibilityCriterion318
