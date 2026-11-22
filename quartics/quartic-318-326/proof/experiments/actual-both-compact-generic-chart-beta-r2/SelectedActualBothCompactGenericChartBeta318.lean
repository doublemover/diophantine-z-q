module

public import SelectedActualLiteralComplexCompactStalkDVR318

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Polynomial
open SelectedActualComplexGenericChartClosures318
open SelectedActualComplexGenericCompactNormal318
open SelectedActualLiteralComplexCompactStalkDVR318

namespace SelectedActualBothCompactGenericChartBeta318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private theorem entireChart_preimage {A F : CommRingCat} {Y : Scheme}
    (φ : A ⟶ F) (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (f : Spec F ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : f = Spec.map φ ≫ j) :
    (⊤ : (Spec F).Opens) ≤
      f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ (j ''ᵁ ⊤)) := by
  rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization, hf]
  exact (NormalizationChart318.whole_preimage φ j).ge

private def chartSections {A F : CommRingCat} {Y : Scheme}
    (φ : A ⟶ F) (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (f : Spec F ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : f = Spec.map φ ≫ j) :
    letI := φ.hom.toAlgebra
    Γ(f.normalization,f.fromNormalization ⁻¹ᵁ (j ''ᵁ ⊤)) ≃+* integralClosure A F := by
  subst f
  exact NormalChart318.sectionsEquiv φ j

private theorem chart_sections_value {A F : CommRingCat} {Y : Scheme}
    (φ : A ⟶ F) (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (f : Spec F ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : f = Spec.map φ ≫ j) :
    letI := φ.hom.toAlgebra
    CommRingCat.ofHom ((Subalgebra.val (integralClosure A F)).toRingHom.comp
      (chartSections φ j f hf).toRingHom) =
      f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ (j ''ᵁ ⊤)) ⊤
        (entireChart_preimage φ j f hf) ≫ (Scheme.ΓSpecIso F).hom := by
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
  have hf : (f.normalizationObjIso hU).hom ≫
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
  unfold chartSections
  rw [hb,hf]
  simp only [NormalizationChart318.sourceSections,Iso.trans_hom,Functor.mapIso_hom,
    ← Category.assoc]
  rw [Scheme.Hom.appLE_map] <;> rfl

variable (F : Type) [Field F] [Algebra JField F]
variable [aF : Algebra ℂ F] [τF : IsScalarTower ℂ JField F]

include aF τF in
/-- The same actual generic point lies on both literal normal charts,
using the already proved reciprocal factor through the projective overlap. -/
theorem whole_generic_on_chart (i : Fin 2) :
    (⊤ : (Spec (CommRingCat.of F)).Opens) ≤
      (genericMap F).toNormalization ⁻¹ᵁ (sourceCover F i).1 :=
  entireChart_preimage (CommRingCat.ofHom (polynomial F i)) (JLineAtlas318.chart ℂ i)
    (genericMap F) (genericMap_factor F i)

include aF τF in
private theorem chartRingEquiv_toRingHom (i : Fin 2) :
    letI := (polynomial F i).toAlgebra
    (chartRingEquiv F i).toRingHom =
      (chartSections (CommRingCat.ofHom (polynomial F i))
        (JLineAtlas318.chart ℂ i) (genericMap F) (genericMap_factor F i)).toRingHom := by
  letI := (polynomial F i).toAlgebra
  apply RingHom.ext
  intro a
  rfl

include aF τF in
/-- The integral-order inclusion selected by the actual compact chart is
the restriction of the same original generic morphism on both chart 1
and chart 0. In particular no new generic point is chosen over infinity. -/
theorem actual_compact_chart_generic_readout (i : Fin 2) :
    let U := (sourceCover F i).1
    letI := (polynomial F i).toAlgebra
    CommRingCat.ofHom ((Subalgebra.val (integralClosure ℂ[X] F)).toRingHom.comp
      (chartRingEquiv F i).toRingHom) =
      (genericMap F).toNormalization.appLE U ⊤ (whole_generic_on_chart F i) ≫
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom := by
  letI := (polynomial F i).toAlgebra
  have hv := chart_sections_value (CommRingCat.ofHom (polynomial F i))
    (JLineAtlas318.chart ℂ i) (genericMap F) (genericMap_factor F i)
  have h := congrArg
    (fun f : chartRing F i →+* integralClosure ℂ[X] F =>
      CommRingCat.ofHom ((Subalgebra.val (integralClosure ℂ[X] F)).toRingHom.comp f))
    (chartRingEquiv_toRingHom F i)
  exact h.trans hv

end SelectedActualBothCompactGenericChartBeta318

#print axioms SelectedActualBothCompactGenericChartBeta318.whole_generic_on_chart
#print axioms SelectedActualBothCompactGenericChartBeta318.actual_compact_chart_generic_readout
