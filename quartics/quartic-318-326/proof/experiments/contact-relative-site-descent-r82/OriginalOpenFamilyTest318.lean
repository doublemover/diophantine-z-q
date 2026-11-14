module
public import ContactFppfCechDescent318
public section
noncomputable section
namespace OriginalOpenFamilyTest318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeLineClassBaseChange318 RelativeSectionBaseChange318
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T : Scheme.{u}} (q : C ⟶ B) (b : T ⟶ B) (U : T.Opens)
abbrev family := pullback q b
abbrev projection := pullback.snd q b
abbrev sourceOpen : (family q b).Opens := projection q b ⁻¹ᵁ U
abbrev test := pullback q (U.ι ≫ b)
abbrev total := totalMap q b (U.ι ≫ b) U.ι rfl

/-- The full original family test on an open base is exactly the actual
inverse-image open subscheme of the original full family. -/
@[expose] def iso : test q b U ≅ (sourceOpen q b U).toScheme :=
  (OriginalTestCoverCartesian318.cartesian q b (U.ι ≫ b) U.ι rfl).isoPullback ≪≫
    pullbackRestrictIsoRestrict (projection q b) U

@[reassoc] lemma iso_hom_ι : (iso q b U).hom ≫ (sourceOpen q b U).ι = total q b U := by
  simp only [iso,Iso.trans_hom,Category.assoc,pullbackRestrictIsoRestrict_hom_ι,
    IsPullback.isoPullback_hom_fst]
@[reassoc] lemma iso_inv_total : (iso q b U).inv ≫ total q b U = (sourceOpen q b U).ι := by
  rw [← iso_hom_ι,Iso.inv_hom_id_assoc]

@[reassoc] lemma iso_hom_projection : (iso q b U).hom ≫ projection q b ∣_ U =
    pullback.snd q (U.ι ≫ b) := by
  simp only [iso,Iso.trans_hom,Category.assoc,pullbackRestrictIsoRestrict_hom_morphismRestrict,
    IsPullback.isoPullback_hom_snd]
@[reassoc] lemma iso_inv_projection : (iso q b U).inv ≫ pullback.snd q (U.ι ≫ b) =
    projection q b ∣_ U := by
  rw [← iso_hom_projection,Iso.inv_hom_id_assoc]

variable (e : B ⟶ C) (hs : e ≫ q = 𝟙 B)

/-- The section of the actual inverse-image open is the original full-test
section transported through this exact open isomorphism. -/
@[expose] def openSection : U.toScheme ⟶ (sourceOpen q b U).toScheme :=
  sectionOn q e hs (U.ι ≫ b) ≫ (iso q b U).hom

@[reassoc] lemma section_projection : openSection q b U e hs ≫ projection q b ∣_ U = 𝟙 _ := by
  rw [openSection,Category.assoc,iso_hom_projection,sectionOn_snd]
@[reassoc] lemma section_ι : openSection q b U e hs ≫ (sourceOpen q b U).ι =
    U.ι ≫ sectionOn q e hs b := by
  rw [openSection,Category.assoc,iso_hom_ι]
  exact sectionOn_naturality q e hs b (U.ι ≫ b) U.ι rfl

/-- The original evaluation map on the actual inverse-image open inherits
the full-test universal global-functions theorem. -/
lemma evaluation_bijective [IsAffine B] [IsProper q] [IsIso q.appTop] [Flat (U.ι ≫ b)] :
    Function.Bijective (openSection q b U e hs).appTop := by
  let : IsIso (pullback.snd q (U.ι ≫ b)).appTop :=
    UniversalStructurePushforward318.baseChange_app_isIso q (U.ι ≫ b) ⊤
  let : IsIso (projection q b ∣_ U).appTop :=
    OriginalSchemeIsoEvaluation318.projection_appTop_isIso (iso q b U).symm
      (projection q b ∣_ U) (pullback.snd q (U.ι ≫ b)) (iso_inv_projection q b U)
  exact UniversalSectionEvaluation318.section_appTop_bijective _ _ (section_projection q b U e hs)
end OriginalOpenFamilyTest318
