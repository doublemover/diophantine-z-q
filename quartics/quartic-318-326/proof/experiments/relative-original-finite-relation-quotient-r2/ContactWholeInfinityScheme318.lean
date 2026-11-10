module
public import ContactWholeInfinityAlgebra318
public import NormalizationBaseCompatibility318

public section
noncomputable section
namespace ContactWholeInfinityScheme318
open AlgebraicGeometry CategoryTheory

/-- Normalize the base square BEFORE specializing the integral closure.
Unlike the trans/refl route, the section equivalence occurs literally on
both sides, so no concrete integral-closure algebra-equivalence reduction
is needed at the contact-model application. -/
private theorem raw_chart_over_base {A B : CommRingCat} {Y : Scheme}
    (φ : A ⟶ B) (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (f : Spec B ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : f = Spec.map φ ≫ j) :
    letI := φ.hom.toAlgebra
    (Spec.map (CommRingCat.ofHom
      (InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf).toRingHom) ≫
      ((NormalizationBaseCompatibility318.target_affine j).preimage
        f.fromNormalization).fromSpec) ≫ f.fromNormalization =
    Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A B))) ≫ j := by
  letI := φ.hom.toAlgebra
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f.fromNormalization
    (NormalizationBaseCompatibility318.target_affine j)
    ((NormalizationBaseCompatibility318.target_affine j).preimage f.fromNormalization) le_rfl]
  rw [← Scheme.Hom.app_eq_appLE, ← Spec.map_comp_assoc,
    NormalizationBaseCompatibility318.factored_sections_base φ j f hf,
    Spec.map_comp, Category.assoc,
    NormalizationBaseCompatibility318.targetSections_fromSpec]

open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
local instance : IsFinite (ContactProjectiveModel318.modelMap c) :=
  ContactGlobalProper318.normalization_finite c

abbrev actualOpen : (ContactProjectiveModel318.model c).affineOpens :=
  ⟨ContactProjectiveModel318.modelMap c ⁻¹ᵁ (JLineAtlas318.chart ℚ 0 ''ᵁ ⊤),
    (NormalizationBaseCompatibility318.target_affine (JLineAtlas318.chart ℚ 0)).preimage _⟩

abbrev chartRing : CommRingCat := Γ(ContactProjectiveModel318.model c,(actualOpen c).1)

/-- Exact sections of the entire original infinity inverse image. -/
def sectionsEquiv : chartRing c ≃+* ContactWholeInfinityAlgebra318.Ring c :=
  InfinityGlobalChart318.sectionsEquiv_of_factor
    (CommRingCat.ofHom (ContactWholeInfinityAlgebra318.polynomialMap c))
    (JLineAtlas318.chart ℚ 0) (ContactProjectiveModel318.coverMap c)
    (ContactGlobalProper318.reciprocal_factor c)

def chartIso : Spec (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) ≅
    Spec (chartRing c) := Scheme.Spec.mapIso (sectionsEquiv c).toCommRingCatIso.op

def into : Spec (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) ⟶
    ContactProjectiveModel318.model c := (chartIso c).hom ≫ (actualOpen c).2.fromSpec

instance : IsOpenImmersion (into c) := by
  unfold into
  infer_instance

lemma into_range : (into c).opensRange = (actualOpen c).1 := by
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (actualOpen c).2.opensRange_fromSpec

def projection : Spec (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) ⟶
    Spec (CommRingCat.of (Polynomial ℚ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (ContactWholeInfinityAlgebra318.Ring c)))

/-- The original normalization section comparison retains the actual
reciprocal base map on the whole infinity chart. -/
lemma over_base : into c ≫ ContactProjectiveModel318.modelMap c =
    projection c ≫ JLineAtlas318.chart ℚ 0 := by
  have h := raw_chart_over_base
    (A := CommRingCat.of (Polynomial ℚ))
    (B := CommRingCat.of (ContactWholeInfinityAlgebra318.Source c))
    (CommRingCat.ofHom (ContactWholeInfinityAlgebra318.polynomialMap c))
    (JLineAtlas318.chart ℚ 0) (ContactProjectiveModel318.coverMap c)
    (ContactGlobalProper318.reciprocal_factor c)
  change into c ≫ ContactProjectiveModel318.modelMap c =
    projection c ≫ JLineAtlas318.chart ℚ 0 at h
  exact h

/-- Genuine entire base change, with no punctures removed from the infinity
polynomial chart. -/
lemma original_pullback : IsPullback (projection c) (into c)
    (JLineAtlas318.chart ℚ 0) (ContactProjectiveModel318.modelMap c) := by
  apply IsOpenImmersion.isPullback
  · exact over_base c
  · rw [into_range,← Scheme.Hom.image_top_eq_opensRange] <;> rfl
end ContactWholeInfinityScheme318
