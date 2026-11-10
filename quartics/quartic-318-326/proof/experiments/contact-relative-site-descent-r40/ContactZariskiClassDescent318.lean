module
public import OriginalGlobalPointedRestriction318
public section
noncomputable section
namespace ContactZariskiClassDescent318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open LineSheafClass318 RelativeLineClassBaseChange318 RelativeLineClassQuotient318
open RigidifiedRelativeClass318 RigidifiedLineIsomorphism318
open OriginalOpenFamilyTest318 OriginalPointedOpenFamily318
open ContactUniversalRigidifiedClass318
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {T : Scheme} (b : T ⟶ FieldBase t) {ι : Type} (U : ι → T.Opens)
  (hc : (⊤ : T.Opens) ≤ iSup U)

include hc in
/-- Equality of original Contact relative classes is detected on every
full Zariski cover, by gluing actual compatible original line isomorphisms. -/
lemma separated (c d : TestClass (q t) b)
    (h : ∀ i, testMap (q t) b ((U i).ι ≫ b) (U i).ι rfl c =
      testMap (q t) b ((U i).ι ≫ b) (U i).ι rfl d) : c = d := by
  let L := RigidifiedClassQuotient318.representative (testSection t b) (pullback.snd (q t) b)
    (RelativeSectionBaseChange318.sectionOn_snd (q t) (e t) (section_eq t) b) c
  let M := RigidifiedClassQuotient318.representative (testSection t b) (pullback.snd (q t) b)
    (RelativeSectionBaseChange318.sectionOn_snd (q t) (e t) (section_eq t) b) d
  have hL := RigidifiedClassQuotient318.representative_class (testSection t b) (pullback.snd (q t) b)
    (RelativeSectionBaseChange318.sectionOn_snd (q t) (e t) (section_eq t) b) c
  have hM := RigidifiedClassQuotient318.representative_class (testSection t b) (pullback.snd (q t) b)
    (RelativeSectionBaseChange318.sectionOn_snd (q t) (e t) (section_eq t) b) d
  have heq (i : ι) : relativeClass (projection (q t) b ∣_ U i) (sec (q t) b (e t) (section_eq t) (U i))
      (OriginalGlobalPointedRestriction318.line (q t) b (e t) (section_eq t) (U i) L) =
    relativeClass (projection (q t) b ∣_ U i) (sec (q t) b (e t) (section_eq t) (U i))
      (OriginalGlobalPointedRestriction318.line (q t) b (e t) (section_eq t) (U i) M) := by
    rw [OriginalGlobalPointedRestriction318.line_class,OriginalGlobalPointedRestriction318.line_class,hL,hM]
    have hh := congrArg (OriginalOpenRelativeClasses318.equivalence (q t) b (U i)) (h i)
    simpa only [OriginalOpenRelativeClasses318.restriction_eq] using hh
  let a := fun i => RigidifiedIsoCoherence318.transition (sec (q t) b (e t) (section_eq t) (U i))
    (projection (q t) b ∣_ U i) (section_projection (q t) b (U i) (e t) (section_eq t))
    (evaluation_bijective (q t) b (U i) (e t) (section_eq t)) (heq i)
  have ha : ∀ i j V (hi : V ≤ sourceOpen (q t) b (U i)) (hj : V ≤ sourceOpen (q t) b (U j)),
      OpenSheafRestrictionCompatibility318.schemeRestrict (a i).iso hi =
        OpenSheafRestrictionCompatibility318.schemeRestrict (a j).iso hj := by
    intro i j V hi hj
    -- It is enough to compare first on the entire inverse-image pair; its
    -- further arbitrary source subopens are then genuine restrictions.
    have hp := compatible_unique (sec (q t) b (e t) (section_eq t) (U i ⊓ U j))
      (evaluation_bijective (q t) b (U i ⊓ U j) (e t) (section_eq t)).injective _ _
      (OriginalGlobalPointedRestriction318.restrictIso (q t) b (e t) (section_eq t) inf_le_left (a i))
      (OriginalGlobalPointedRestriction318.restrictIso (q t) b (e t) (section_eq t) inf_le_right (a j))
    have hp' := congrArg (fun z => z.iso) hp
    rw [OriginalGlobalPointedRestriction318.restrictIso_iso,
      OriginalGlobalPointedRestriction318.restrictIso_iso] at hp'
    apply OpenSchemeTransition318.toOver_injective
    rw [OpenSheafRestrictionCompatibility318.restriction_compatible,
      OpenSheafRestrictionCompatibility318.restriction_compatible]
    have hpo := congrArg (OpenChartModuleImages318.toOverIso
      (sourceOpen (q t) b (U i ⊓ U j))) hp'
    rw [OpenSheafRestrictionCompatibility318.restriction_compatible,
      OpenSheafRestrictionCompatibility318.restriction_compatible] at hpo
    have hz := congrArg (fun z => OpenSheafTransition318.restrictIso z (le_inf hi hj)) hpo
    simpa only [OriginalOpenIsoGluing318.restrict_twice] using hz
  let z := OriginalOpenIsoGluing318.iso (fun i => sourceOpen (q t) b (U i))
    (fun i => (a i).iso) ha (OriginalOpenClassGluing318.source_cover (q t) b U hc)
  have hz := congrArg (RelativeLineClassQuotient318.classMap (pullback.snd (q t) b)) (classOf_eq z)
  exact hL.symm.trans (hz.trans hM)

include hc in
/-- The actual original Contact relative-class presheaf has unique gluing
for arbitrary Zariski open covers, with standard original testMap matching. -/
theorem matching_unique (c : ∀ i, TestClass (q t) ((U i).ι ≫ b))
    (hm : ∀ i j,
      testMap (q t) ((U i).ι ≫ b) ((U i ⊓ U j).ι ≫ b)
          (T.homOfLE (show U i ⊓ U j ≤ U i from inf_le_left))
          (OriginalOpenTestNaturality318.test_path b inf_le_left) (c i) =
        testMap (q t) ((U j).ι ≫ b) ((U i ⊓ U j).ι ≫ b)
          (T.homOfLE (show U i ⊓ U j ≤ U j from inf_le_right))
          (OriginalOpenTestNaturality318.test_path b inf_le_right) (c j)) :
    ∃! d : TestClass (q t) b, ∀ i, testMap (q t) b ((U i).ι ≫ b) (U i).ι rfl d = c i := by
  obtain ⟨d,hd⟩ := ContactZariskiClassExistence318.exists_class t b U hc c hm
  exact ⟨d,hd,fun d' hd' => separated t b U hc d' d (fun i => (hd' i).trans (hd i).symm)⟩
end ContactZariskiClassDescent318
