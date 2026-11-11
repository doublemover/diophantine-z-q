module
public import OriginalTestTripleIso318
public section
noncomputable section
namespace OriginalTestNerveEvaluation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineClassBaseChange318 RelativeSectionBaseChange318
open ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318 OriginalTestCechCoordinates318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T T' : Scheme.{u}} (q : C ⟶ B) (e : B ⟶ C) (hs : e ≫ q = 𝟙 B)
  (b : T ⟶ B) (b' : T' ⟶ B) (g : T' ⟶ T) (hg : g ≫ b = b')
abbrev localSection := sectionOn q e hs b'
abbrev baseSection := sectionOn q e hs b
abbrev pointed := sectionOn_naturality q e hs b b' g hg
abbrev doubleSection := RigidifiedCechNerve318.doubleSection (f q b b' g hg) g
  (baseSection q e hs b) (localSection q e hs b') (pointed q e hs b b' g hg)
abbrev tripleSection := RigidifiedCechNerve318.tripleSection (f q b b' g hg) g
  (baseSection q e hs b) (localSection q e hs b') (pointed q e hs b b' g hg)

lemma double_section : doubleSection q e hs b b' g hg ≫ doubleProjection q b b' g hg = 𝟙 _ :=
  RigidifiedCechNerve318.double_section (f q b b' g hg) g (baseSection q e hs b)
    (localSection q e hs b') (pointed q e hs b b' g hg) (p q b) (p' q b')
    (sectionOn_snd q e hs b') (totalMap_snd q b b' g hg).symm

lemma triple_section : tripleSection q e hs b b' g hg ≫ tripleProjection q b b' g hg = 𝟙 _ := by
  apply triple_hom_ext g
  · rw [Category.assoc,OriginalTestCechCoordinates318.triple_vertex0,
      ← Category.assoc,ActualDescentBaseChangeDiagram318.triple_vertex0,
      Category.assoc,sectionOn_snd,Category.comp_id,Category.id_comp]
  · rw [Category.assoc,OriginalTestCechCoordinates318.triple_vertex1,
      ← Category.assoc,ActualDescentBaseChangeDiagram318.triple_vertex1,
      Category.assoc,sectionOn_snd,Category.comp_id,Category.id_comp]
  · rw [Category.assoc,OriginalTestCechCoordinates318.triple_vertex2,
      ← Category.assoc,ActualDescentBaseChangeDiagram318.triple_vertex2,
      Category.assoc,sectionOn_snd,Category.comp_id,Category.id_comp]

/-- Rigidity on the actual categorical double follows from its exact full
test presentation and the original universal global-functions theorem. -/
lemma double_evaluation [IsAffine B] [IsProper q] [IsIso q.appTop]
    [Flat (OriginalTestDoubleIso318.base b' g)] :
    Function.Bijective (doubleSection q e hs b b' g hg).appTop := by
  let : IsIso (pullback.snd q (OriginalTestDoubleIso318.base b' g)).appTop :=
    UniversalStructurePushforward318.baseChange_app_isIso q (OriginalTestDoubleIso318.base b' g) ⊤
  let : IsIso (doubleProjection q b b' g hg).appTop :=
    OriginalSchemeIsoEvaluation318.projection_appTop_isIso (OriginalTestDoubleIso318.iso q b b' g hg)
      (doubleProjection q b b' g hg) (pullback.snd q (OriginalTestDoubleIso318.base b' g))
      (OriginalTestDoubleIso318.iso_projection q b b' g hg)
  exact UniversalSectionEvaluation318.section_appTop_bijective _ _ (double_section q e hs b b' g hg)

/-- The same argument covers the full actual triple, including nonaffine
and nonreduced tests. No evaluation hypothesis is assumed on the nerve. -/
lemma triple_evaluation [IsAffine B] [IsProper q] [IsIso q.appTop]
    [Flat (OriginalTestTripleIso318.base b' g)] :
    Function.Bijective (tripleSection q e hs b b' g hg).appTop := by
  let : IsIso (pullback.snd q (OriginalTestTripleIso318.base b' g)).appTop :=
    UniversalStructurePushforward318.baseChange_app_isIso q (OriginalTestTripleIso318.base b' g) ⊤
  let : IsIso (tripleProjection q b b' g hg).appTop :=
    OriginalSchemeIsoEvaluation318.projection_appTop_isIso (OriginalTestTripleIso318.iso q b b' g hg)
      (tripleProjection q b b' g hg) (pullback.snd q (OriginalTestTripleIso318.base b' g))
      (OriginalTestTripleIso318.iso_projection q b b' g hg)
  exact UniversalSectionEvaluation318.section_appTop_bijective _ _ (triple_section q e hs b b' g hg)
end OriginalTestNerveEvaluation318
