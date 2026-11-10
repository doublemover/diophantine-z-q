module
public import ContactWholeInfinityScheme318
public import ContactOriginalLineFiniteChart318
public import LineSheafPullback318

public section
noncomputable section
namespace ContactOriginalLineBothCharts318
open AlgebraicGeometry CategoryTheory LineSheafClass318
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- The same arbitrary global original line on the whole finite chart. -/
abbrev finiteLine := LineSheafPullback318.line (SourceGlobalAffine318.chartEmbedding c) L

/-- The same arbitrary global original line on the whole infinity chart. -/
abbrev infinityLine := LineSheafPullback318.line (ContactWholeInfinityScheme318.into c) L

abbrev finiteSections := ContactOriginalLineFiniteChart318.sections c (finiteLine c L)
abbrev infinitySections := OriginalLineFiniteFlatPID318.pushed
  (CommRingCat.of (Polynomial ℚ)) (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c))
  (infinityLine c L)

instance finiteSections_finite : Module.Finite (Polynomial ℚ) (finiteSections c L) :=
  ContactOriginalLineFiniteChart318.finite c (finiteLine c L)
instance finiteSections_free : Module.Free (Polynomial ℚ) (finiteSections c L) :=
  ContactOriginalLineFiniteChart318.free c (finiteLine c L)
instance infinitySections_finite : Module.Finite (Polynomial ℚ) (infinitySections c L) :=
  OriginalLineFiniteFlatPID318.finite (CommRingCat.of (Polynomial ℚ))
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) (infinityLine c L)
instance infinitySections_free : Module.Free (Polynomial ℚ) (infinitySections c L) :=
  OriginalLineFiniteFlatPID318.free (CommRingCat.of (Polynomial ℚ))
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) (infinityLine c L)

/-- Actual finite coordinates on the original finite-chart sections. -/
def finiteCoordinates : finiteSections c L ≃ₗ[Polynomial ℚ]
    (Fin (Module.finrank (Polynomial ℚ) (finiteSections c L)) → Polynomial ℚ) :=
  ContactOriginalLineFiniteChart318.coordinates c (finiteLine c L)

/-- Actual finite coordinates on the original entire infinity-chart sections.
This is produced for every original L and is not a free-transition input. -/
def infinityCoordinates : infinitySections c L ≃ₗ[Polynomial ℚ]
    (Fin (Module.finrank (Polynomial ℚ) (infinitySections c L)) → Polynomial ℚ) :=
  OriginalLineFiniteFlatPID318.coordinates (CommRingCat.of (Polynomial ℚ))
    (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) (infinityLine c L)

lemma infinity_object : (infinityLine c L).object =
    (Scheme.Modules.pullback (ContactWholeInfinityScheme318.into c)).obj L.object := rfl

/-- Both chosen opens cover the whole original Contact model. -/
lemma whole_cover : (SourceGlobalAffine318.chartEmbedding c).opensRange ⊔
    (ContactWholeInfinityScheme318.into c).opensRange = ⊤ := by
  rw [SourceGlobalAffine318.chartEmbedding_range,ContactWholeInfinityScheme318.into_range]
  change ContactProjectiveModel318.modelMap c ⁻¹ᵁ (JLineAtlas318.chart ℚ 1 ''ᵁ ⊤) ⊔
    ContactProjectiveModel318.modelMap c ⁻¹ᵁ (JLineAtlas318.chart ℚ 0 ''ᵁ ⊤) = ⊤
  have h := ContactGlobalProper318.targetCover_covers
  have htwo : (⨆ i : Fin 2, JLineAtlas318.chart ℚ i ''ᵁ ⊤) =
      (JLineAtlas318.chart ℚ 0 ''ᵁ ⊤) ⊔ (JLineAtlas318.chart ℚ 1 ''ᵁ ⊤) := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i <;> simp
    · exact sup_le (le_iSup _ 0) (le_iSup _ 1)
  change (⨆ i : Fin 2, JLineAtlas318.chart ℚ i ''ᵁ ⊤) = ⊤ at h
  rw [htwo] at h
  rw [← Scheme.Hom.preimage_sup,sup_comm,h,Scheme.Hom.preimage_top]
end ContactOriginalLineBothCharts318
