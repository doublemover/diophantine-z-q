module
public import ContactZariskiClassExistence318
public section
noncomputable section
namespace OriginalGlobalPointedRestriction318
open AlgebraicGeometry CategoryTheory RelativeRigidifiedLine318 RigidifiedLineIsomorphism318
open RigidifiedRelativeClass318 RelativeLineClassQuotient318 OriginalOpenFamilyTest318
open OriginalPointedOpenFamily318
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T : Scheme.{u}} (q : C ⟶ B) (b : T ⟶ B) (e : B ⟶ C) (hs : e ≫ q = 𝟙 B)
abbrev globalSection := RelativeSectionBaseChange318.sectionOn q e hs b

@[expose] def line (U : T.Opens) (L : RigidifiedLine (globalSection q b e hs)) :
    RigidifiedLine (sec q b e hs U) :=
  RigidifiedOpenRestriction318.line (globalSection q b e hs) (sec q b e hs U)
    (sourceOpen q b U).ι U.ι (section_ι q b U e hs) L

lemma line_class (U : T.Opens) (L : RigidifiedLine (globalSection q b e hs)) :
    relativeClass (projection q b ∣_ U) (sec q b e hs U) (line q b e hs U L) =
      OriginalOpenRelativeClasses318.restriction q b U
        (relativeClass (projection q b) (globalSection q b e hs) L) := by
  have hh := congrArg (RelativeLineClassQuotient318.classMap (projection q b ∣_ U))
    (LineSheafClass318.classOf_eq (RigidifiedOpenRestriction318.comparison
      (globalSection q b e hs) (sec q b e hs U) (sourceOpen q b U).ι U.ι
      (section_ι q b U e hs) L).iso)
  exact hh.trans (RigidifiedPointedPullback318.relativeClass_line (globalSection q b e hs)
    (sec q b e hs U) (sourceOpen q b U).ι U.ι (section_ι q b U e hs)
    (projection q b) (projection q b ∣_ U) (morphismRestrict_ι (projection q b) U).symm L)

@[expose] def composition {U V : T.Opens} (h : V ≤ U)
    (L : RigidifiedLine (globalSection q b e hs)) : CompatibleIso (sec q b e hs V)
    (OriginalPointedOpenFamily318.line q b e hs h (line q b e hs U L)) (line q b e hs V L) :=
  RigidifiedRestrictionComposition318.path (globalSection q b e hs) (sec q b e hs U) (sec q b e hs V)
    (sourceOpen q b U).ι (inclusion q b h) (sourceOpen q b V).ι
    U.ι (T.homOfLE h) V.ι (section_ι q b U e hs) (pointed q b e hs h) (section_ι q b V e hs)
    (Scheme.homOfLE_ι _ _) (Scheme.homOfLE_ι _ _) L

lemma composition_iso {U V : T.Opens} (h : V ≤ U)
    (L : RigidifiedLine (globalSection q b e hs)) :
    (composition q b e hs h L).iso =
      (OpenSheafRestrictionCompatibility318.path L.line.object ((projection q b).preimage_mono h)).symm := by
  apply Iso.ext
  apply (cancel_epi (OpenSheafRestrictionCompatibility318.path L.line.object
    ((projection q b).preimage_mono h)).hom).mp
  have hh := RigidifiedRestrictionComposition318.path_hom
    (globalSection q b e hs) (sec q b e hs U) (sec q b e hs V)
    (sourceOpen q b U).ι (inclusion q b h) (sourceOpen q b V).ι
    U.ι (T.homOfLE h) V.ι (section_ι q b U e hs) (pointed q b e hs h) (section_ι q b V e hs)
    (Scheme.homOfLE_ι _ _) (Scheme.homOfLE_ι _ _) L
  change _ ≫ (composition q b e hs h L).iso.hom = _
  rw [hh,OpenRestrictionPathNormalization318.path_collapse]
  exact (OpenSheafRestrictionCompatibility318.path L.line.object
    ((projection q b).preimage_mono h)).hom_inv_id.symm

@[expose] def restrictIso {U V : T.Opens} (h : V ≤ U)
    {L M : RigidifiedLine (globalSection q b e hs)}
    (a : CompatibleIso (sec q b e hs U) (line q b e hs U L) (line q b e hs U M)) :
    CompatibleIso (sec q b e hs V) (line q b e hs V L) (line q b e hs V M) :=
  RigidifiedIsoCoherence318.compose _ (RigidifiedIsoCoherence318.inverse _ (composition q b e hs h L))
    (RigidifiedIsoCoherence318.compose _ (OriginalPointedOpenFamily318.mapIso q b e hs h a)
      (composition q b e hs h M))

lemma restrictIso_iso {U V : T.Opens} (h : V ≤ U)
    {L M : RigidifiedLine (globalSection q b e hs)}
    (a : CompatibleIso (sec q b e hs U) (line q b e hs U L) (line q b e hs U M)) :
    (restrictIso q b e hs h a).iso =
      OpenSheafRestrictionCompatibility318.schemeRestrict a.iso ((projection q b).preimage_mono h) := by
  simp only [restrictIso,RigidifiedIsoCoherence318.compose,RigidifiedIsoCoherence318.inverse,
    composition_iso,Iso.symm_symm,OpenSheafRestrictionCompatibility318.schemeRestrict] <;> rfl
end OriginalGlobalPointedRestriction318
