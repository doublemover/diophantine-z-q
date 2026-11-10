module
public import OriginalOpenIsoGluing318
public section
noncomputable section
namespace OriginalPointedOpenFamily318
open AlgebraicGeometry CategoryTheory RelativeRigidifiedLine318 RigidifiedLineIsomorphism318
open RigidifiedRelativeClass318 RelativeLineClassQuotient318 OriginalOpenFamilyTest318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T : Scheme.{u}} (q : C ⟶ B) (b : T ⟶ B) (e : B ⟶ C) (hs : e ≫ q = 𝟙 B)
  {U V W : T.Opens}
abbrev sec (U : T.Opens) := OriginalOpenFamilyTest318.openSection q b U e hs
abbrev inclusion (h : V ≤ U) := (family q b).homOfLE ((projection q b).preimage_mono h)

lemma pointed (h : V ≤ U) : sec q b e hs V ≫ inclusion q b h = T.homOfLE h ≫ sec q b e hs U := by
  apply (cancel_mono (sourceOpen q b U).ι).mp
  rw [Category.assoc,Scheme.homOfLE_ι,section_ι,Category.assoc,section_ι,
    ← Category.assoc,Scheme.homOfLE_ι]

@[expose] def line (h : V ≤ U) (L : RigidifiedLine (sec q b e hs U)) :
    RigidifiedLine (sec q b e hs V) :=
  RigidifiedOpenRestriction318.line (sec q b e hs U) (sec q b e hs V)
    (inclusion q b h) (T.homOfLE h) (pointed q b e hs h) L

@[expose] def mapIso (h : V ≤ U) {L M : RigidifiedLine (sec q b e hs U)}
    (a : CompatibleIso (sec q b e hs U) L M) :
    CompatibleIso (sec q b e hs V) (line q b e hs h L) (line q b e hs h M) :=
  RigidifiedOpenRestriction318.mapIso (sec q b e hs U) (sec q b e hs V)
    (inclusion q b h) (T.homOfLE h) (pointed q b e hs h) a

@[expose] def classMap (h : V ≤ U) :
    RelativeClass (projection q b ∣_ U) →* RelativeClass (projection q b ∣_ V) :=
  RelativeLineClassQuotient318.map (projection q b ∣_ U) (projection q b ∣_ V)
    (inclusion q b h) (T.homOfLE h) (morphismRestrict_homOfLE (projection q b) V U h).symm

lemma line_class (h : V ≤ U) (L : RigidifiedLine (sec q b e hs U)) :
    relativeClass (projection q b ∣_ V) (sec q b e hs V) (line q b e hs h L) =
      classMap q b h (relativeClass (projection q b ∣_ U) (sec q b e hs U) L) := by
  have hh := congrArg (RelativeLineClassQuotient318.classMap (projection q b ∣_ V))
    (LineSheafClass318.classOf_eq (RigidifiedOpenRestriction318.comparison
      (sec q b e hs U) (sec q b e hs V) (inclusion q b h) (T.homOfLE h)
      (pointed q b e hs h) L).iso)
  exact hh.trans (RigidifiedPointedPullback318.relativeClass_line (sec q b e hs U)
    (sec q b e hs V) (inclusion q b h) (T.homOfLE h) (pointed q b e hs h)
    (projection q b ∣_ U) (projection q b ∣_ V)
    (morphismRestrict_homOfLE (projection q b) V U h).symm L)

/-- The literal nested restrictions are compared by the original
restriction collapse, with their specified actual section rigidifications. -/
@[expose] def composition (h : V ≤ U) (k : W ≤ V) (L : RigidifiedLine (sec q b e hs U)) :
    CompatibleIso (sec q b e hs W) (line q b e hs k (line q b e hs h L))
      (line q b e hs (k.trans h) L) :=
  RigidifiedRestrictionComposition318.path (sec q b e hs U) (sec q b e hs V) (sec q b e hs W)
    (inclusion q b h) (inclusion q b k) (inclusion q b (k.trans h))
    (T.homOfLE h) (T.homOfLE k) (T.homOfLE (k.trans h))
    (pointed q b e hs h) (pointed q b e hs k) (pointed q b e hs (k.trans h))
    (OriginalOpenPullbackComposition318.inclusion_comp _ _)
    (OriginalOpenPullbackComposition318.inclusion_comp k h) L

lemma composition_iso (h : V ≤ U) (k : W ≤ V) (L : RigidifiedLine (sec q b e hs U)) :
    (composition q b e hs h k L).iso =
      (OpenRestrictionPathCoherence318.collapse ((projection q b).preimage_mono k)
        ((projection q b).preimage_mono h)).app L.line.object := by
  apply Iso.ext
  exact RigidifiedRestrictionComposition318.path_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
end OriginalPointedOpenFamily318
