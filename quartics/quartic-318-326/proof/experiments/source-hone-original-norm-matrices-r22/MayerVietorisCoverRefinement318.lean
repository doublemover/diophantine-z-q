module
public import SchemeBoundaryNaturality318

public section
noncomputable section
namespace MayerVietorisCoverRefinement318
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open LocalSheafCohomologySections318 LocalSheafCohomologyAdditive318 LocalCohomologyRestriction318
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{0}}

theorem generator_comp {U V W : Opens X} (i : U ⟶ V) (j : V ⟶ W) :
    generatorMap (i ≫ j) = generatorMap i ≫ generatorMap j := by
  simp [generatorMap,freeMap]

variable (U V U' V' : Opens X) (h : U ⊔ V = ⊤) (h' : U' ⊔ V' = ⊤)
  (hU : U' ≤ U) (hV : V' ≤ V)

/-- A refinement maps the actual short exact generator sequences, preserving chart order and difference sign. -/
@[expose] def shortComplexMap :
    (OpenMayerVietoris318.mayerVietoris U' V' h').shortComplex ⟶
      (OpenMayerVietoris318.mayerVietoris U V h).shortComplex where
  τ₁ := generatorMap (homOfLE (inf_le_inf hU hV))
  τ₂ := biprod.map (generatorMap (homOfLE hU)) (generatorMap (homOfLE hV))
  τ₃ := 𝟙 _
  comm₁₂ := by
    change generatorMap (homOfLE (inf_le_inf hU hV)) ≫
      biprod.lift (generatorMap (homOfLE inf_le_left : U ⊓ V ⟶ U))
        (-generatorMap (homOfLE inf_le_right : U ⊓ V ⟶ V)) =
      biprod.lift (generatorMap (homOfLE inf_le_left : U' ⊓ V' ⟶ U'))
        (-generatorMap (homOfLE inf_le_right : U' ⊓ V' ⟶ V')) ≫
        biprod.map (generatorMap (homOfLE hU)) (generatorMap (homOfLE hV))
    apply biprod.hom_ext
    · simp only [Category.assoc,biprod.lift_fst,biprod.map_fst]
      simp only [← Category.assoc,biprod.lift_fst,← generator_comp]
      all_goals congr 1
    · simp only [Category.assoc,biprod.lift_snd,biprod.map_snd,Preadditive.comp_neg]
      simp only [← Category.assoc,biprod.lift_snd,Preadditive.neg_comp,← generator_comp]
      all_goals congr 1
  comm₂₃ := by
    change biprod.map (generatorMap (homOfLE hU)) (generatorMap (homOfLE hV)) ≫
      biprod.desc (generatorMap (homOfLE le_top : U ⟶ ⊤))
        (generatorMap (homOfLE le_top : V ⟶ ⊤)) =
      biprod.desc (generatorMap (homOfLE le_top : U' ⟶ ⊤))
        (generatorMap (homOfLE le_top : V' ⟶ ⊤)) ≫ 𝟙 _
    apply biprod.hom_ext'
    · simp only [← Category.assoc,biprod.inl_map,Category.comp_id]
      simp only [Category.assoc,biprod.inl_desc,← generator_comp]
      all_goals congr 1
    · simp only [← Category.assoc,biprod.inr_map,Category.comp_id]
      simp only [Category.assoc,biprod.inr_desc,← generator_comp]
      all_goals congr 1

/-- The actual extension class of a refined cover maps to the original class. -/
theorem extClass_refinement :
    (OpenMayerVietoris318.mayerVietoris U' V' h').shortComplex_shortExact.extClass.comp
      (Ext.mk₀ (generatorMap (homOfLE (inf_le_inf hU hV)))) (add_zero 1) =
    (OpenMayerVietoris318.mayerVietoris U V h).shortComplex_shortExact.extClass := by
  have he := ShortComplex.ShortExact.extClass_naturality
    (OpenMayerVietoris318.mayerVietoris U' V' h').shortComplex_shortExact
    (OpenMayerVietoris318.mayerVietoris U V h).shortComplex_shortExact
    (shortComplexMap U V U' V' h h' hU hV)
  simpa only [shortComplexMap,Ext.mk₀_id_comp] using he

/-- Boundary naturality for actual cover refinement, with no equality-of-preimages assumption. -/
theorem boundary_refinement (F : ASheaf (X:=X)) (x : F.H' 0 (U ⊓ V)) :
    OpenMayerVietoris318.boundary F U' V' h'
      ((F.cohomologyPresheaf 0).map (homOfLE (inf_le_inf hU hV)).op x) =
    OpenMayerVietoris318.boundary F U V h x := by
  change TerminalLocalCohomology318.equivalence X F 1
    ((OpenMayerVietoris318.mayerVietoris U' V' h').shortComplex_shortExact.extClass.comp
      ((Ext.mk₀ (generatorMap (homOfLE (inf_le_inf hU hV)))).comp x (zero_add 0))
      (by decide)) = _
  rw [← Ext.comp_assoc_of_second_deg_zero,extClass_refinement U V U' V' h h' hU hV]
  rfl

/-- The same refinement identity on the original regular-section representatives. -/
theorem sectionBoundary_refinement (F : ASheaf (X:=X)) (x : F.obj.obj (op (U ⊓ V))) :
    MayerVietorisSectionKernel318.sectionBoundary F U' V' h'
      (F.obj.map (homOfLE (inf_le_inf hU hV)).op x) =
    MayerVietorisSectionKernel318.sectionBoundary F U V h x := by
  have hz : (zeroAddEquiv F (U' ⊓ V')).symm
      (F.obj.map (homOfLE (inf_le_inf hU hV)).op x) =
    (F.cohomologyPresheaf 0).map (homOfLE (inf_le_inf hU hV)).op
      ((zeroAddEquiv F (U ⊓ V)).symm x) := by
    apply (zeroAddEquiv F (U' ⊓ V')).injective
    rw [AddEquiv.apply_symm_apply,LocalCohomologyRestriction318.zero_naturality,
      AddEquiv.apply_symm_apply]
  change OpenMayerVietoris318.boundary F U' V' h'
    ((zeroAddEquiv F (U' ⊓ V')).symm _) = _
  rw [hz,boundary_refinement U V U' V' h h' hU hV F]
  rfl

end MayerVietorisCoverRefinement318
