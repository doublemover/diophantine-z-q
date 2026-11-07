module
public import ProperOpenJNormalization318
public import Mathlib.AlgebraicGeometry.Noetherian
public section
noncomputable section
namespace NormalChart318
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {A B:CommRingCat.{u}} {Y:Scheme.{u}} (φ:A⟶B)
  (c:Spec A⟶Y) [IsOpenImmersion c]
  [QuasiCompact (Spec.map φ≫c)] [QuasiSeparated (Spec.map φ≫c)]

/-- Exact ring of sections on the actual normalization chart, identified with
the concrete chart's integral closure, including both base/ambient changes. -/
@[expose] def sectionsEquiv :
    letI:=φ.hom.toAlgebra
    Γ((Spec.map φ≫c).normalization,
      (Spec.map φ≫c).fromNormalization⁻¹ᵁ(c ''ᵁ ⊤))≃+*integralClosure A B := by
  letI:=φ.hom.toAlgebra
  letI:=((Spec.map φ≫c).app (c ''ᵁ ⊤)).hom.toAlgebra
  have hs : (NormalizationChart318.targetSections c).inv ≫ (Spec.map φ≫c).app (c ''ᵁ ⊤) =
      φ ≫ (NormalizationChart318.sourceSections φ c).inv := by
    rw [←cancel_mono (NormalizationChart318.sourceSections φ c).hom]
    simp only [Category.assoc,NormalizationChart318.section_square,Iso.inv_hom_id,
      Category.comp_id,Iso.inv_hom_id_assoc]
  let e:=IntegralClosureSquare318.closureEquiv
    (NormalizationChart318.targetSections c).symm.commRingCatIsoToRingEquiv
    (NormalizationChart318.sourceSections φ c).symm.commRingCatIsoToRingEquiv
    (congrArg CommRingCat.Hom.hom hs)
  have hc:IsAffineOpen (c ''ᵁ ⊤):=by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange c
  exact ((Spec.map φ≫c).normalizationObjIso hc).commRingCatIsoToRingEquiv.trans e.symm

/-- Normality of the actual normalization chart's sections is derived from
the proved concrete integral closure, rather than assumed of a global model. -/
theorem normal_sections
    (hn:letI:=φ.hom.toAlgebra;IsIntegrallyClosed (integralClosure A B)) :
    IsIntegrallyClosed Γ((Spec.map φ≫c).normalization,
      (Spec.map φ≫c).fromNormalization⁻¹ᵁ(c ''ᵁ ⊤)) := by
  letI:=φ.hom.toAlgebra
  letI:=hn
  exact IsIntegrallyClosed.of_equiv (sectionsEquiv φ c).symm

theorem noetherian_sections
    (hn:letI:=φ.hom.toAlgebra;IsNoetherianRing (integralClosure A B)) :
    IsNoetherianRing Γ((Spec.map φ≫c).normalization,
      (Spec.map φ≫c).fromNormalization⁻¹ᵁ(c ''ᵁ ⊤)) := by
  letI:=φ.hom.toAlgebra
  letI:=hn
  exact isNoetherianRing_of_ringEquiv _ (sectionsEquiv φ c).symm

theorem domain_sections [IsDomain B] :
    IsDomain Γ((Spec.map φ≫c).normalization,
      (Spec.map φ≫c).fromNormalization⁻¹ᵁ(c ''ᵁ ⊤)) := by
  letI:=φ.hom.toAlgebra
  exact MulEquiv.isDomain _ (sectionsEquiv φ c).toMulEquiv

theorem properties_of_factor [IsDomain B]
    (f : Spec B ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : f=Spec.map φ≫c)
    (hn : letI:=φ.hom.toAlgebra;
      IsIntegrallyClosed (integralClosure A B) ∧ IsNoetherianRing (integralClosure A B)) :
    IsDomain Γ(f.normalization,f.fromNormalization⁻¹ᵁ(c ''ᵁ ⊤)) ∧
    IsIntegrallyClosed Γ(f.normalization,f.fromNormalization⁻¹ᵁ(c ''ᵁ ⊤)) ∧
    IsNoetherianRing Γ(f.normalization,f.fromNormalization⁻¹ᵁ(c ''ᵁ ⊤)) := by
  subst f
  exact ⟨domain_sections φ c,normal_sections φ c hn.1,noetherian_sections φ c hn.2⟩

end NormalChart318
