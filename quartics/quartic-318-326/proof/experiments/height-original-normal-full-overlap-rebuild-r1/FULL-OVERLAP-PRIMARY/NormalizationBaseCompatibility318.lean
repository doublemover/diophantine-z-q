module
public import InfinityGlobalScheme318
public section
noncomputable section
namespace NormalizationBaseCompatibility318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B:CommRingCat} {Y:Scheme}
  (φ:A⟶B) (j:Spec A⟶Y) [IsOpenImmersion j]
  [QuasiCompact (Spec.map φ≫j)] [QuasiSeparated (Spec.map φ≫j)]

theorem target_affine : IsAffineOpen (j ''ᵁ ⊤) := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange j

/-- The actual normalization chart section equivalence preserves the
actual base section map, including the chart's change of coefficient ring. -/
theorem sections_base :
    letI:=φ.hom.toAlgebra
    (Spec.map φ≫j).fromNormalization.app (j ''ᵁ ⊤)≫
      CommRingCat.ofHom (NormalChart318.sectionsEquiv φ j).toRingHom=
    (NormalizationChart318.targetSections j).hom≫
      CommRingCat.ofHom (algebraMap A (integralClosure A B)) := by
  letI:=φ.hom.toAlgebra
  letI:=((Spec.map φ≫j).app (j ''ᵁ ⊤)).hom.toAlgebra
  have hs:(NormalizationChart318.targetSections j).inv≫(Spec.map φ≫j).app (j ''ᵁ ⊤)=
      φ≫(NormalizationChart318.sourceSections φ j).inv := by
    rw [←cancel_mono (NormalizationChart318.sourceSections φ j).hom]
    simp only [Category.assoc,NormalizationChart318.section_square,Iso.inv_hom_id,
      Category.comp_id,Iso.inv_hom_id_assoc]
  let a: A≃+*Γ(Y,j ''ᵁ ⊤):=
    (NormalizationChart318.targetSections j).symm.commRingCatIsoToRingEquiv
  let b: B≃+*Γ(Spec B,(Spec.map φ≫j)⁻¹ᵁ(j ''ᵁ ⊤)):=
    (NormalizationChart318.sourceSections φ j).symm.commRingCatIsoToRingEquiv
  let e:=IntegralClosureSquare318.closureEquiv a b (congrArg CommRingCat.Hom.hom hs)
  have he:CommRingCat.ofHom (NormalChart318.sectionsEquiv φ j).toRingHom=
      ((Spec.map φ≫j).normalizationObjIso (target_affine j)).hom≫
        CommRingCat.ofHom e.symm.toRingHom := by rfl
  rw [he,Scheme.Hom.fromNormalization_app _ (target_affine j)]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  apply CommRingCat.hom_ext
  exact (IntegralClosureSquare318.inverse_square a e
    (IntegralClosureSquare318.closure_square a b (congrArg CommRingCat.Hom.hom hs))).symm

/-- The coefficient-ring identification for an actual open chart recovers
that same open-chart morphism. -/
theorem targetSections_fromSpec :
    Spec.map (NormalizationChart318.targetSections j).hom≫(target_affine j).fromSpec=j := by
  simp only [NormalizationChart318.targetSections,Iso.trans_hom,Spec.map_comp,Category.assoc,
    Scheme.Hom.appIso_hom']
  rw [IsAffineOpen.SpecMap_appLE_fromSpec j (target_affine j) (isAffineOpen_top (Spec A))]
  simp [IsAffineOpen.fromSpec_top,←Scheme.isoSpec_Spec_hom]

end NormalizationBaseCompatibility318

namespace NormalizationBaseCompatibility318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem factored_sections_base {A B:CommRingCat} {Y:Scheme}
    (φ:A⟶B) (j:Spec A⟶Y) [IsOpenImmersion j]
    (f:Spec B⟶Y) [QuasiCompact f] [QuasiSeparated f] (hf:f=Spec.map φ≫j) :
    letI:=φ.hom.toAlgebra
    f.fromNormalization.app (j ''ᵁ ⊤)≫
      CommRingCat.ofHom (InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf).toRingHom=
    (NormalizationChart318.targetSections j).hom≫
      CommRingCat.ofHom (algebraMap A (integralClosure A B)) := by
  subst f
  exact sections_base φ j
end NormalizationBaseCompatibility318

namespace NormalizationBaseCompatibility318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B C:CommRingCat} {Y:Scheme}
  (φ:A⟶B) (j:Spec A⟶Y) [IsOpenImmersion j]
  (f:Spec B⟶Y) [QuasiCompact f] [QuasiSeparated f] (hf:f=Spec.map φ≫j)
variable [Algebra A C]

/-- Composing with any base-preserving identification of the integral closure
preserves the actual normalization's base section map. -/
theorem factored_sections_base_trans :
    letI:=φ.hom.toAlgebra
    ∀e:integralClosure A B≃ₐ[A]C,
    f.fromNormalization.app (j ''ᵁ ⊤)≫
      CommRingCat.ofHom ((InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf).trans
        e.toRingEquiv).toRingHom=
    (NormalizationChart318.targetSections j).hom≫CommRingCat.ofHom (algebraMap A C) := by
  letI:=φ.hom.toAlgebra
  intro e
  change f.fromNormalization.app (j ''ᵁ ⊤)≫
      (CommRingCat.ofHom (InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf).toRingHom≫
        CommRingCat.ofHom e.toRingHom)=_
  rw [←Category.assoc,factored_sections_base φ j f hf,Category.assoc]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact e.commutes x

/-- The chart obtained from an identification of the actual normalization
section ring commutes with its specified morphism to the base scheme. -/
theorem factored_chart_over_base :
    letI:=φ.hom.toAlgebra
    ∀e:integralClosure A B≃ₐ[A]C,
    (Spec.map (CommRingCat.ofHom
      ((InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf).trans e.toRingEquiv).toRingHom)≫
      ((target_affine j).preimage f.fromNormalization).fromSpec)≫f.fromNormalization=
    Spec.map (CommRingCat.ofHom (algebraMap A C))≫j := by
  letI:=φ.hom.toAlgebra
  intro e
  rw [Category.assoc,←IsAffineOpen.SpecMap_appLE_fromSpec f.fromNormalization
    (target_affine j) ((target_affine j).preimage f.fromNormalization) le_rfl]
  rw [←Scheme.Hom.app_eq_appLE,←Spec.map_comp_assoc,
    factored_sections_base_trans φ j f hf e,Spec.map_comp,Category.assoc,
    targetSections_fromSpec]
end NormalizationBaseCompatibility318
