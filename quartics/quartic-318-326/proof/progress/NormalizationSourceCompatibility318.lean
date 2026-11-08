module
public import NormalizationBaseCompatibility318
public section
noncomputable section
namespace NormalizationSourceCompatibility318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {A B:CommRingCat.{u}} {Y:Scheme.{u}}
  (φ:A⟶B) (j:Spec A⟶Y) [IsOpenImmersion j]
  [QuasiCompact (Spec.map φ≫j)] [QuasiSeparated (Spec.map φ≫j)]

/-- The actual normalization chart's ambient map, rather than only its base
map, recovers the original normalization open morphism. -/
theorem sections_ambient :
    letI:=φ.hom.toAlgebra
    CommRingCat.ofHom (NormalChart318.sectionsEquiv φ j).toRingHom≫
      CommRingCat.ofHom (integralClosure A B).val.toRingHom=
    (Spec.map φ≫j).toNormalization.appLE
      ((Spec.map φ≫j).fromNormalization⁻¹ᵁ(j ''ᵁ ⊤))
      ((Spec.map φ≫j)⁻¹ᵁ(j ''ᵁ ⊤)) (by simp [←Scheme.Hom.comp_preimage])≫
      (NormalizationChart318.sourceSections φ j).hom:=by
  letI:=φ.hom.toAlgebra
  letI:=((Spec.map φ≫j).app (j ''ᵁ ⊤)).hom.toAlgebra
  have hs:(NormalizationChart318.targetSections j).inv≫(Spec.map φ≫j).app (j ''ᵁ ⊤)=
      φ≫(NormalizationChart318.sourceSections φ j).inv:=by
    rw [←cancel_mono (NormalizationChart318.sourceSections φ j).hom]
    simp only [Category.assoc,NormalizationChart318.section_square,Iso.inv_hom_id,
      Category.comp_id,Iso.inv_hom_id_assoc]
  let a:A≃+*Γ(Y,j ''ᵁ ⊤):=(NormalizationChart318.targetSections j).symm.commRingCatIsoToRingEquiv
  let b:B≃+*Γ(Spec B,(Spec.map φ≫j)⁻¹ᵁ(j ''ᵁ ⊤)):=
    (NormalizationChart318.sourceSections φ j).symm.commRingCatIsoToRingEquiv
  let e:=IntegralClosureSquare318.closureEquiv a b (congrArg CommRingCat.Hom.hom hs)
  have he:CommRingCat.ofHom (NormalChart318.sectionsEquiv φ j).toRingHom=
      ((Spec.map φ≫j).normalizationObjIso (NormalizationBaseCompatibility318.target_affine j)).hom≫
        CommRingCat.ofHom e.symm.toRingHom:=by rfl
  have hv:CommRingCat.ofHom e.symm.toRingHom≫CommRingCat.ofHom (integralClosure A B).val.toRingHom=
      CommRingCat.ofHom (integralClosure Γ(Y,j ''ᵁ ⊤)
        Γ(Spec B,(Spec.map φ≫j)⁻¹ᵁ(j ''ᵁ ⊤))).val.toRingHom≫
          (NormalizationChart318.sourceSections φ j).hom:=by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rfl
  rw [he,Category.assoc,hv,←Category.assoc,Scheme.Hom.normalizationObjIso_hom_val]

theorem sourceSections_fromSpec
    (hW:IsAffineOpen ((Spec.map φ≫j)⁻¹ᵁ(j ''ᵁ ⊤))) :
    Spec.map (NormalizationChart318.sourceSections φ j).hom≫hW.fromSpec=𝟙 (Spec B):=by
  simp only [NormalizationChart318.sourceSections,Iso.trans_hom,Functor.mapIso_hom,
    Spec.map_comp,Category.assoc]
  rw [IsAffineOpen.map_fromSpec hW (isAffineOpen_top (Spec B))]
  simp [IsAffineOpen.fromSpec_top,←Scheme.isoSpec_Spec_hom]

/-- The whole original affine source maps into its actual normalization
chart by the literal integral-closure inclusion, after the specified chart iso. -/
theorem chart_original {C:CommRingCat.{u}} [Algebra A C] :
    letI:=φ.hom.toAlgebra
    ∀ e:integralClosure A B≃ₐ[A]C,
    Spec.map (CommRingCat.ofHom ((integralClosure A B).val.toRingHom.comp e.symm.toRingHom))≫
      (Spec.map (CommRingCat.ofHom ((NormalChart318.sectionsEquiv φ j).trans e.toRingEquiv).toRingHom)≫
        ((NormalizationBaseCompatibility318.target_affine j).preimage
          (Spec.map φ≫j).fromNormalization).fromSpec)=
      (Spec.map φ≫j).toNormalization:=by
  letI:=φ.hom.toAlgebra
  intro e
  have hs:CommRingCat.ofHom ((NormalChart318.sectionsEquiv φ j).trans e.toRingEquiv).toRingHom≫
      CommRingCat.ofHom ((integralClosure A B).val.toRingHom.comp e.symm.toRingHom)=
    CommRingCat.ofHom (NormalChart318.sectionsEquiv φ j).toRingHom≫
      CommRingCat.ofHom (integralClosure A B).val.toRingHom:=by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change (↑(e.symm (e ((NormalChart318.sectionsEquiv φ j) x))):B)=_
    rw [e.symm_apply_apply]
    rfl
  rw [←Category.assoc,←Spec.map_comp,hs,sections_ambient,Spec.map_comp,Category.assoc]
  have hW:IsAffineOpen ((Spec.map φ≫j)⁻¹ᵁ(j ''ᵁ ⊤)):=by
    rw [NormalizationChart318.whole_preimage]
    exact isAffineOpen_top _
  rw [IsAffineOpen.SpecMap_appLE_fromSpec _ _ hW,←Category.assoc,
    sourceSections_fromSpec φ j hW]
  exact Category.id_comp _

omit [QuasiCompact (Spec.map φ≫j)] [QuasiSeparated (Spec.map φ≫j)] in
theorem factored_chart_original {C:CommRingCat.{u}} [Algebra A C]
    (f:Spec B⟶Y) [QuasiCompact f] [QuasiSeparated f] (hf:f=Spec.map φ≫j) :
    letI:=φ.hom.toAlgebra
    ∀e:integralClosure A B≃ₐ[A]C,
    Spec.map (CommRingCat.ofHom ((integralClosure A B).val.toRingHom.comp e.symm.toRingHom))≫
      (Spec.map (CommRingCat.ofHom
        ((InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf).trans e.toRingEquiv).toRingHom)≫
        ((NormalizationBaseCompatibility318.target_affine j).preimage f.fromNormalization).fromSpec)=
      f.toNormalization:=by
  subst f
  exact chart_original φ j

end NormalizationSourceCompatibility318
