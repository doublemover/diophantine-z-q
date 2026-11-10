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
/-- Naturality stated directly for the additive equivalence, with its
actual inverse cancelled before changing to plain section coordinates. -/
lemma sectionHom_post {F G : ASheaf (X := X)} (f : F ⟶ G)
    (W : X.Opens) (s : F.obj.obj (op W)) :
    sectionAddEquiv G W (sectionHom F W s ≫ f) = f.hom.app (op W) s := by
  change sectionEquiv G W (sectionHom F W s ≫ f) = _
  rw [sectionEquiv_naturality]
  change f.hom.app (op W) ((sectionAddEquiv F W) ((sectionAddEquiv F W).symm s)) = _
  rw [AddEquiv.apply_symm_apply]
lemma sectionHom_pre (F : ASheaf (X := X)) {W Z : X.Opens} (f : W ⟶ Z)
    (s : F.obj.obj (op Z)) :
    sectionAddEquiv F W (generatorMap f ≫ sectionHom F Z s) = F.obj.map f.op s := by
  change sectionEquiv F W (generatorMap f ≫ sectionHom F Z s) = _
  rw [section_naturality]
  change F.obj.map f.op ((sectionAddEquiv F Z) ((sectionAddEquiv F Z).symm s)) = _
  rw [AddEquiv.apply_symm_apply]
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
    rw [sectionHom_post,sectionHom_pre,sectionHom_pre]
    simpa only [difference,AdditiveSheafSections318.res,
      TwoOpenAdditiveCocycle318.opens,sub_eq_add_neg] using coefficient_spec a false true
  comm₂₃ := by
    apply biprod.hom_ext'
    · change biprod.inl ≫ biprod.desc (sectionHom (I X) U (a.value false))
        (sectionHom (I X) V (a.value true)) ≫ projection X =
        biprod.inl ≫ biprod.desc (generatorMap (homOfLE le_top : U ⟶ ⊤))
          (generatorMap (homOfLE le_top : V ⟶ ⊤)) ≫ sectionHom (Q X) ⊤ t
      simp only [biprod.inl_desc_assoc]
      apply (sectionAddEquiv (Q X) U).injective
      rw [sectionHom_post,sectionHom_pre]
      simpa only [AdditiveSheafSections318.res,TwoOpenAdditiveCocycle318.opens] using a.image false
    · change biprod.inr ≫ biprod.desc (sectionHom (I X) U (a.value false))
        (sectionHom (I X) V (a.value true)) ≫ projection X =
        biprod.inr ≫ biprod.desc (generatorMap (homOfLE le_top : U ⟶ ⊤))
          (generatorMap (homOfLE le_top : V ⟶ ⊤)) ≫ sectionHom (Q X) ⊤ t
      simp only [biprod.inr_desc_assoc]
      apply (sectionAddEquiv (Q X) V).injective
      rw [sectionHom_post,sectionHom_pre]
      simpa only [AdditiveSheafSections318.res,TwoOpenAdditiveCocycle318.opens] using a.image true
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
