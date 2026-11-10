module
public import LocalCohomologyRestriction318
public import TerminalLocalCohomology318

public section
noncomputable section
namespace InverseImageLocalGenerator318
open CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite
open LocalSheafCohomologySections318 SheafInverseImageConstants318
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The original inverse-image adjunction represents sections over the actual inverse-image open. -/
@[expose] def sectionMate (U : Opens Y) (F : ASheaf (X:=X)) :
    ((inverseImage f).obj (generator U) ⟶ F) ≃ F.obj.obj (op ((Opens.map f).obj U)) :=
  ((adjunction f).homEquiv _ _).trans (sectionEquiv ((directImage f).obj F) U)

theorem sectionMate_naturality (U : Opens Y) {F G : ASheaf (X:=X)}
    (a : F ⟶ G) (b : (inverseImage f).obj (generator U) ⟶ F) :
    sectionMate f U G (b ≫ a) =
      a.hom.app (op ((Opens.map f).obj U)) (sectionMate f U F b) := by
  exact (congrArg (sectionEquiv ((directImage f).obj G) U)
    ((adjunction f).homEquiv_naturality_right b a)).trans
      (sectionEquiv_naturality ((directImage f).map a) U _)

/-- The same comparison respects the actual restriction arrows, not merely open sets. -/
theorem sectionMate_restriction {U V : Opens Y} (i : U ⟶ V) (F : ASheaf (X:=X))
    (a : (inverseImage f).obj (generator V) ⟶ F) :
    sectionMate f U F ((inverseImage f).map (LocalCohomologyRestriction318.generatorMap i) ≫ a) =
      F.obj.map ((Opens.map f).map i).op (sectionMate f V F a) := by
  exact (congrArg (sectionEquiv ((directImage f).obj F) U)
    ((adjunction f).homEquiv_naturality_left
      (LocalCohomologyRestriction318.generatorMap i) a)).trans
      (LocalCohomologyRestriction318.section_naturality ((directImage f).obj F) i _)

@[expose] def generatorHom (U : Opens Y) :
    (inverseImage f).obj (generator U) ⟶ generator ((Opens.map f).obj U) :=
  (sectionMate f U _).symm (sectionEquiv _ ((Opens.map f).obj U) (𝟙 _))

@[expose] def generatorInv (U : Opens Y) :
    generator ((Opens.map f).obj U) ⟶ (inverseImage f).obj (generator U) :=
  (sectionEquiv _ ((Opens.map f).obj U)).symm (sectionMate f U _ (𝟙 _))

theorem generatorInv_section (U : Opens Y) (F : ASheaf (X:=X))
    (a : (inverseImage f).obj (generator U) ⟶ F) :
    sectionEquiv F ((Opens.map f).obj U) (generatorInv f U ≫ a) =
      sectionMate f U F a := by
  rw [sectionEquiv_naturality]
  change a.hom.app _ ((sectionEquiv _ _)
      ((sectionEquiv _ _).symm (sectionMate f U _ (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply]
  simpa only [Category.id_comp] using (sectionMate_naturality f U a (𝟙 _)).symm

theorem generatorHom_section (U : Opens Y) (F : ASheaf (X:=X))
    (a : generator ((Opens.map f).obj U) ⟶ F) :
    sectionMate f U F (generatorHom f U ≫ a) =
      sectionEquiv F ((Opens.map f).obj U) a := by
  rw [sectionMate_naturality]
  change a.hom.app _ ((sectionMate f U _)
      ((sectionMate f U _).symm (sectionEquiv _ _ (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply]
  simpa only [Category.id_comp] using (sectionEquiv_naturality a _ (𝟙 _)).symm

/-- Actual local free generators commute with inverse image; both directions are fixed by sections. -/
@[expose] def generatorIso (U : Opens Y) :
    (inverseImage f).obj (generator U) ≅ generator ((Opens.map f).obj U) where
  hom := generatorHom f U
  inv := generatorInv f U
  hom_inv_id := by
    apply (sectionMate f U _).injective
    rw [generatorHom_section]
    exact (sectionEquiv _ _).apply_symm_apply _
  inv_hom_id := by
    apply (sectionEquiv _ _).injective
    rw [generatorInv_section]
    exact (sectionMate f U _).apply_symm_apply _

/-- Compatibility of the constructed isomorphism with every original restriction map. -/
theorem generatorInv_naturality {U V : Opens Y} (i : U ⟶ V) :
    LocalCohomologyRestriction318.generatorMap ((Opens.map f).map i) ≫ generatorInv f V =
      generatorInv f U ≫ (inverseImage f).map (LocalCohomologyRestriction318.generatorMap i) := by
  apply (sectionEquiv _ ((Opens.map f).obj U)).injective
  rw [LocalCohomologyRestriction318.section_naturality,generatorInv_section]
  rw [show sectionEquiv _ ((Opens.map f).obj V) (generatorInv f V) =
    sectionMate f V _ (𝟙 _) from (sectionEquiv _ _).apply_symm_apply _]
  simpa only [Category.comp_id] using
    (sectionMate_restriction f i _ (𝟙 _)).symm

end InverseImageLocalGenerator318
