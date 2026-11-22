module

public import SelectedActualComplexGenericCompactNormal318

public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open SelectedActualComplexGenericChartClosures318
open SelectedActualComplexGenericCompactNormal318

namespace SelectedActualCuspCanonicalChartReadout318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Package the chart isomorphism with the section-map calculation before
specializing the factorization. No equality between two transported chart
isomorphisms is involved. -/
private theorem sections_with_readout_of_factor {A F : CommRingCat} {Y : Scheme}
    (φ : A ⟶ F) (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (f : Spec F ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : f = Spec.map φ ≫ j)
    (htop : (⊤ : (Spec F).Opens) ≤ f.toNormalization ⁻¹ᵁ
      (f.fromNormalization ⁻¹ᵁ (j ''ᵁ ⊤))) :
    letI := φ.hom.toAlgebra
    ∃ e : Γ(f.normalization,f.fromNormalization ⁻¹ᵁ (j ''ᵁ ⊤)) ≃+* integralClosure A F,
      CommRingCat.ofHom ((Subalgebra.val (integralClosure A F)).toRingHom.comp
        e.toRingHom) =
      f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ (j ''ᵁ ⊤)) ⊤
        htop ≫ (Scheme.ΓSpecIso F).hom := by
  subst f
  let f := Spec.map φ ≫ j
  let U : Y.Opens := j ''ᵁ ⊤
  let V : f.normalization.Opens := f.fromNormalization ⁻¹ᵁ U
  letI := φ.hom.toAlgebra
  letI := (f.app U).hom.toAlgebra
  have hU : IsAffineOpen U := by
    change IsAffineOpen (j ''ᵁ ⊤)
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange j
  have hF : f ⁻¹ᵁ U = (⊤ : (Spec F).Opens) := NormalizationChart318.whole_preimage φ j
  have hV : f.toNormalization ⁻¹ᵁ V = (⊤ : (Spec F).Opens) := by
    change f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) = ⊤
    rw [← Scheme.Hom.comp_preimage, f.toNormalization_fromNormalization, hF]
  have h₀ : f ⁻¹ᵁ U ≤ f.toNormalization ⁻¹ᵁ V := by rw [hF,hV]
  have hEval : (f.normalizationObjIso hU).hom ≫
      CommRingCat.ofHom (Subalgebra.val
        (integralClosure Γ(Y,U) Γ(Spec F, f ⁻¹ᵁ U))).toRingHom =
        f.toNormalization.appLE V (f ⁻¹ᵁ U) h₀ :=
    f.normalizationObjIso_hom_val hU
  have hb : CommRingCat.ofHom ((Subalgebra.val (integralClosure A F)).toRingHom.comp
      (NormalChart318.sectionsEquiv φ j).toRingHom) =
      ((f.normalizationObjIso hU).hom ≫
        CommRingCat.ofHom (Subalgebra.val
          (integralClosure Γ(Y,U) Γ(Spec F, f ⁻¹ᵁ U))).toRingHom) ≫
            (NormalizationChart318.sourceSections φ j).hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    unfold NormalChart318.sectionsEquiv
    rfl
  refine ⟨NormalChart318.sectionsEquiv φ j, ?_⟩
  rw [hb,hEval]
  simp only [NormalizationChart318.sourceSections,Iso.trans_hom,Functor.mapIso_hom,
    ← Category.assoc]
  rw [Scheme.Hom.appLE_map]

variable (F : Type) [Field F] [Algebra JField F]
variable [aC : Algebra ℂ F] [tC : IsScalarTower ℂ JField F]

include aC tC in
/-- The actual whole generic point lies on chart zero of its normalization. -/
theorem generic_at_reciprocal_chart :
    (⊤ : (Spec (CommRingCat.of F)).Opens) ≤
      (genericMap F).toNormalization ⁻¹ᵁ (sourceCover F 0).1 := by
  change ⊤ ≤ (genericMap F).toNormalization ⁻¹ᵁ
    ((genericMap F).fromNormalization ⁻¹ᵁ (JLineAtlas318.chart ℂ (0 : Fin 2) ''ᵁ ⊤))
  rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization,
    genericMap_factor F 0]
  exact (NormalizationChart318.whole_preimage (CommRingCat.ofHom (polynomial F 0))
    (JLineAtlas318.chart ℂ 0)).ge

include aC tC in
/-- A witness on the actual reciprocal affine chart of the original
normalization, paired with its exact same-whole-field readout. A caller
uses this witness itself for its character prime and the scheme stalk. -/
theorem exists_actual_reciprocal_chart_with_readout :
    let U := (sourceCover F 0).1
    letI := (polynomial F 0).toAlgebra
    ∃ e : Γ(model F,U) ≃+* integralClosure ℂ[X] F,
      CommRingCat.ofHom ((Subalgebra.val (integralClosure ℂ[X] F)).toRingHom.comp
        e.toRingHom) =
      (genericMap F).toNormalization.appLE U ⊤ (generic_at_reciprocal_chart F) ≫
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom := by
  letI := (polynomial F 0).toAlgebra
  exact sections_with_readout_of_factor (CommRingCat.ofHom (polynomial F 0))
    (JLineAtlas318.chart ℂ 0) (genericMap F) (genericMap_factor F 0)
    (generic_at_reciprocal_chart F)

end SelectedActualCuspCanonicalChartReadout318

#print axioms SelectedActualCuspCanonicalChartReadout318.generic_at_reciprocal_chart
#print axioms SelectedActualCuspCanonicalChartReadout318.exists_actual_reciprocal_chart_with_readout
