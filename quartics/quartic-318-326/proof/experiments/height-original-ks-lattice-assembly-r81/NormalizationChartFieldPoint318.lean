module
public import NormalizationSourceCompatibility318
public section
noncomputable section
namespace NormalizationChartFieldPoint318
open CategoryTheory AlgebraicGeometry
universe u
variable {A B F : CommRingCat.{u}} {Y : Scheme.{u}}
  (φ : A ⟶ B) (j : Spec A ⟶ Y) [IsOpenImmersion j]
  (f : Spec B ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  (hf : f = Spec.map φ ≫ j)

/-- The canonical point of the original normalization coming from any
specified ambient homomorphism B→F is recovered on each factor chart by
its EXACT integral-closure inclusion. No comparison of abstract fields and
no equality of finite and reciprocal parameter actions is required. -/
theorem canonical_chart_point (h : B ⟶ F) :
    letI := φ.hom.toAlgebra
    Spec.map (CommRingCat.ofHom (h.hom.comp (integralClosure A B).val.toRingHom)) ≫
      (Spec.map (CommRingCat.ofHom
        (InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf).toRingHom) ≫
        ((NormalizationBaseCompatibility318.target_affine j).preimage
          f.fromNormalization).fromSpec) = Spec.map h ≫ f.toNormalization := by
  letI := φ.hom.toAlgebra
  have hs := NormalizationSourceCompatibility318.factored_chart_original
    (C := CommRingCat.of (integralClosure A B)) φ j f hf (AlgEquiv.refl : integralClosure A B ≃ₐ[A] integralClosure A B)
  change Spec.map (CommRingCat.ofHom (integralClosure A B).val.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom
      (InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf).toRingHom) ≫
      ((NormalizationBaseCompatibility318.target_affine j).preimage
        f.fromNormalization).fromSpec) = f.toNormalization at hs
  rw [← hs]
  simp only [← Category.assoc, ← Spec.map_comp] <;> rfl

end NormalizationChartFieldPoint318
