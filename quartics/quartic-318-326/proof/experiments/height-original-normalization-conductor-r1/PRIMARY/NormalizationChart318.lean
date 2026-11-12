module
public import IntegralClosureSquare318
public import GlobalNormalization318
public section
noncomputable section
namespace NormalizationChart318
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {A B:CommRingCat.{u}} {Y:Scheme.{u}}
  (φ:A⟶B) (c:Spec A⟶Y) [IsOpenImmersion c]

lemma whole_preimage : (Spec.map φ≫c)⁻¹ᵁ(c ''ᵁ ⊤)=⊤ := by
  rw [Scheme.Hom.comp_preimage,c.preimage_image_eq]
  simp

@[expose] def targetSections : Γ(Y,c ''ᵁ ⊤)≅A := c.appIso ⊤ ≪≫ Scheme.ΓSpecIso A
@[expose] def sourceSections : Γ(Spec B,(Spec.map φ≫c)⁻¹ᵁ(c ''ᵁ ⊤))≅B :=
  (Spec B).presheaf.mapIso (eqToIso (whole_preimage φ c).symm).op ≪≫ Scheme.ΓSpecIso B

lemma section_square : (Spec.map φ≫c).app (c ''ᵁ ⊤) ≫ (sourceSections φ c).hom =
    (targetSections c).hom ≫ φ := by
  simp only [sourceSections,targetSections,Iso.trans_hom,Functor.mapIso_hom,
    Scheme.Hom.appIso_hom']
  rw [←Category.assoc,Category.assoc _ _ φ]
  change (Spec.map φ≫c).appLE (c ''ᵁ ⊤) ⊤ (by rw [whole_preimage]) ≫ (Scheme.ΓSpecIso B).hom =
    c.appLE (c ''ᵁ ⊤) ⊤ (by rw [c.preimage_image_eq]) ≫ (Scheme.ΓSpecIso A).hom ≫ φ
  rw [← Scheme.ΓSpecIso_naturality φ, ←Category.assoc]
  congr 1

/-- The proved finite integral closure of a concrete chart homomorphism is
transported into the actual global normalization's section-ring interface. -/
theorem finite_sections
    (hf : letI:=φ.hom.toAlgebra; Module.Finite A (integralClosure A B)) :
    letI:=((Spec.map φ≫c).app (c ''ᵁ ⊤)).hom.toAlgebra
    Module.Finite Γ(Y,c ''ᵁ ⊤)
      (integralClosure Γ(Y,c ''ᵁ ⊤) Γ(Spec B,(Spec.map φ≫c)⁻¹ᵁ(c ''ᵁ ⊤))) := by
  letI:=φ.hom.toAlgebra
  letI:=((Spec.map φ≫c).app (c ''ᵁ ⊤)).hom.toAlgebra
  letI:=hf
  apply IntegralClosureSquare318.finite
    (targetSections c).symm.commRingCatIsoToRingEquiv
    (sourceSections φ c).symm.commRingCatIsoToRingEquiv
  have hs : (targetSections c).inv ≫ (Spec.map φ≫c).app (c ''ᵁ ⊤) =
      φ ≫ (sourceSections φ c).inv := by
    rw [←cancel_mono (sourceSections φ c).hom]
    simp only [Category.assoc,section_square,Iso.inv_hom_id,Category.comp_id,
      Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom hs

end NormalizationChart318
