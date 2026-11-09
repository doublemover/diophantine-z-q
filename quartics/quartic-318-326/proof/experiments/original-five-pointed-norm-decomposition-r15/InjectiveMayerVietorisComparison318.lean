module
public import InjectiveCoverPointed318
public section
noncomputable section
namespace InjectiveMayerVietorisComparison318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite LocalSheafCohomologySections318 LocalSheafCohomologyAdditive318
open OriginalStructureInjectivePresentation318 InjectiveCoverCocycle318
open LocalCohomologyRestriction318
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} (U V : X.Opens) (h : U ⊔ V = ⊤)
    {t : (Q X).obj.obj (op ⊤)} (a : Lifts X (TwoOpenAdditiveCocycle318.opens U V) t)
@[expose] def sectionHom (F : ASheaf (X := X)) (W : X.Opens) (s : F.obj.obj (op W)) :
    generator W ⟶ F := (sectionAddEquiv F W).symm s
lemma sectionHom_value (F : ASheaf (X := X)) (W : X.Opens) (s : F.obj.obj (op W)) :
    sectionAddEquiv F W (sectionHom F W s) = s := (sectionAddEquiv F W).apply_symm_apply s
lemma sectionHom_ext (F : ASheaf (X := X)) (W : X.Opens) (s : F.obj.obj (op W)) :
    Ext.mk₀ (sectionHom F W s) = (zeroAddEquiv F W).symm s := rfl
/-- Exact short-complex map from the ORIGINAL Mayer-Vietoris free-generator
sequence to the actual injective presentation of the ORIGINAL structure sheaf. -/
@[expose] def shortComplexMap :
    (OpenMayerVietoris318.mayerVietoris U V h).shortComplex ⟶ sequence X where
  τ₁ := sectionHom (O X) (U ⊓ V) (coefficient a false true)
  τ₂ := biprod.desc (sectionHom (I X) U (a.value false)) (sectionHom (I X) V (a.value true))
  τ₃ := sectionHom (Q X) ⊤ t
  comm₁₂ := by
    change sectionHom (O X) (U ⊓ V) (coefficient a false true) ≫ inclusion X =
      biprod.lift (generatorMap (homOfLE inf_le_left : U ⊓ V ⟶ U))
        (-generatorMap (homOfLE inf_le_right : U ⊓ V ⟶ V)) ≫
      biprod.desc (sectionHom (I X) U (a.value false)) (sectionHom (I X) V (a.value true))
    simp only [biprod.lift_eq, Preadditive.add_comp, Preadditive.neg_comp,
      Category.assoc, biprod.inl_desc, biprod.inr_desc]
    apply (sectionAddEquiv (I X) (U ⊓ V)).injective
    rw [map_add, map_neg]
    change sectionEquiv (I X) (U ⊓ V) (sectionHom (O X) (U ⊓ V) _ ≫ inclusion X) =
      sectionEquiv (I X) (U ⊓ V) (generatorMap _ ≫ sectionHom (I X) U _) -
      sectionEquiv (I X) (U ⊓ V) (generatorMap _ ≫ sectionHom (I X) V _)
    rw [sectionEquiv_naturality, section_naturality, section_naturality]
    simpa only [sectionHom, AddEquiv.apply_symm_apply] using coefficient_spec a false true
  comm₂₃ := by
    apply biprod.hom_ext'
    · change biprod.inl ≫ biprod.desc (sectionHom (I X) U (a.value false))
        (sectionHom (I X) V (a.value true)) ≫ projection X =
        biprod.inl ≫ biprod.desc (generatorMap (homOfLE le_top : U ⟶ ⊤))
          (generatorMap (homOfLE le_top : V ⟶ ⊤)) ≫ sectionHom (Q X) ⊤ t
      simp only [biprod.inl_desc_assoc]
      apply (sectionAddEquiv (Q X) U).injective
      change sectionEquiv (Q X) U (_ ≫ projection X) = sectionEquiv (Q X) U (generatorMap _ ≫ _)
      rw [sectionEquiv_naturality, section_naturality]
      simpa only [sectionHom, AddEquiv.apply_symm_apply] using a.image false
    · change biprod.inr ≫ biprod.desc (sectionHom (I X) U (a.value false))
        (sectionHom (I X) V (a.value true)) ≫ projection X =
        biprod.inr ≫ biprod.desc (generatorMap (homOfLE le_top : U ⟶ ⊤))
          (generatorMap (homOfLE le_top : V ⟶ ⊤)) ≫ sectionHom (Q X) ⊤ t
      simp only [biprod.inr_desc_assoc]
      apply (sectionAddEquiv (Q X) V).injective
      change sectionEquiv (Q X) V (_ ≫ projection X) = sectionEquiv (Q X) V (generatorMap _ ≫ _)
      rw [sectionEquiv_naturality, section_naturality]
      simpa only [sectionHom, AddEquiv.apply_symm_apply] using a.image true
/-- No conventional sign is guessed: both sides are the actual original Ext
classes, joined by the preceding exact short-complex map. -/
lemma boundary_coefficient :
    AffineCoverHOnePresentation318.boundary U V h (coefficient a false true) = boundary X t := by
  have he := ShortComplex.ShortExact.extClass_naturality
    (OpenMayerVietoris318.mayerVietoris U V h).shortComplex_shortExact (shortExact X)
    (shortComplexMap U V h a)
  change (OpenMayerVietoris318.mayerVietoris U V h).shortComplex_shortExact.extClass.comp
      (Ext.mk₀ (sectionHom (O X) (U ⊓ V) (coefficient a false true))) (add_zero 1) =
    (Ext.mk₀ (sectionHom (Q X) ⊤ t)).comp (shortExact X).extClass (zero_add 1) at he
  rw [sectionHom_ext, sectionHom_ext] at he
  exact congrArg (TerminalLocalCohomology318.equivalence X (O X) 1) he
end InjectiveMayerVietorisComparison318
