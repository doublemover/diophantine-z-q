module
public import OriginalLaurentProjectiveOverlap318
public import ContactOriginalLineBothCharts318

public section
noncomputable section
namespace ContactOriginalLaurentOverlap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
local instance : IsFinite (ContactProjectiveModel318.modelMap c) :=
  ContactGlobalProper318.normalization_finite c

/-- The whole original Contact inverse image of the original Laurent overlap. -/
abbrev scheme := pullback (ContactProjectiveModel318.modelMap c)
  OriginalLaurentProjectiveOverlap318.embedding
abbrev into := pullback.fst (ContactProjectiveModel318.modelMap c)
  OriginalLaurentProjectiveOverlap318.embedding
abbrev projection := pullback.snd (ContactProjectiveModel318.modelMap c)
  OriginalLaurentProjectiveOverlap318.embedding

instance : IsAffine (scheme c) := isAffine_of_isAffineHom (projection c)
instance : IsOpenImmersion (into c) := inferInstance

lemma finite_pullback : IsPullback (ContactBicanonicalDegree318.affineMap c)
    (SourceGlobalAffine318.chartEmbedding c) (JLineAtlas318.chart ℚ 1)
    (ContactProjectiveModel318.modelMap c) := by
  simpa only [ContactBicanonicalProjectiveMap318.projectiveMap_eq] using
    ContactBicanonicalDegree318.affine_pullback c

lemma finite_square : projection c ≫ OriginalLaurentProjectiveOverlap318.finiteInclusion ≫
    JLineAtlas318.chart ℚ 1 = into c ≫ ContactProjectiveModel318.modelMap c :=
  (pullback.condition (f := ContactProjectiveModel318.modelMap c)
    (g := OriginalLaurentProjectiveOverlap318.embedding)).symm

lemma infinity_square : projection c ≫ OriginalLaurentProjectiveOverlap318.infinityInclusion ≫
    JLineAtlas318.chart ℚ 0 = into c ≫ ContactProjectiveModel318.modelMap c := by
  rw [← OriginalLaurentProjectiveOverlap318.maps_agree]
  exact finite_square c

/-- The actual original map into the whole finite chart, obtained from its
proved entire base-change square. -/
def finiteEdge : scheme c ⟶ Spec (CommRingCat.of (ContactKummerOrder318.SourceOrder c)) :=
  (finite_pullback c).lift
    (projection c ≫ OriginalLaurentProjectiveOverlap318.finiteInclusion) (into c)
    (by simpa only [Category.assoc] using finite_square c)

/-- The actual original map into the whole infinity chart, obtained from
its proved entire base-change square. -/
def infinityEdge : scheme c ⟶ Spec (CommRingCat.of (ContactWholeInfinityAlgebra318.Ring c)) :=
  (ContactWholeInfinityScheme318.original_pullback c).lift
    (projection c ≫ OriginalLaurentProjectiveOverlap318.infinityInclusion) (into c)
    (by simpa only [Category.assoc] using infinity_square c)

@[reassoc] lemma finiteEdge_into : finiteEdge c ≫ SourceGlobalAffine318.chartEmbedding c = into c :=
  (finite_pullback c).lift_snd _ _ _
@[reassoc] lemma infinityEdge_into : infinityEdge c ≫ ContactWholeInfinityScheme318.into c = into c :=
  (ContactWholeInfinityScheme318.original_pullback c).lift_snd _ _ _
@[reassoc] lemma finiteEdge_projection : finiteEdge c ≫ ContactBicanonicalDegree318.affineMap c =
    projection c ≫ OriginalLaurentProjectiveOverlap318.finiteInclusion :=
  (finite_pullback c).lift_fst _ _ _
@[reassoc] lemma infinityEdge_projection : infinityEdge c ≫ ContactWholeInfinityScheme318.projection c =
    projection c ≫ OriginalLaurentProjectiveOverlap318.infinityInclusion :=
  (ContactWholeInfinityScheme318.original_pullback c).lift_fst _ _ _

instance finiteEdge_open : IsOpenImmersion (finiteEdge c) := by
  haveI : IsOpenImmersion (finiteEdge c ≫ SourceGlobalAffine318.chartEmbedding c) := by
    rw [finiteEdge_into]
    infer_instance
  exact IsOpenImmersion.of_comp (finiteEdge c) (SourceGlobalAffine318.chartEmbedding c)
instance infinityEdge_open : IsOpenImmersion (infinityEdge c) := by
  haveI : IsOpenImmersion (infinityEdge c ≫ ContactWholeInfinityScheme318.into c) := by
    rw [infinityEdge_into]
    infer_instance
  exact IsOpenImmersion.of_comp (infinityEdge c) (ContactWholeInfinityScheme318.into c)

/-- No point of the original chart intersection is discarded: the source is
exactly its entire inverse image, not the old punctured etale cover. -/
lemma full_intersection : (into c).opensRange =
    (SourceGlobalAffine318.chartEmbedding c).opensRange ⊓
      (ContactWholeInfinityScheme318.into c).opensRange := by
  rw [Scheme.Hom.opensRange_pullbackFst,← OriginalLaurentProjectiveOverlap318.full_intersection,
    Scheme.Hom.preimage_inf,SourceGlobalAffine318.chartEmbedding_range,
    ContactWholeInfinityScheme318.into_range]
  simp only [SourceGlobalAffine318.actualOpen,Scheme.Hom.image_top_eq_opensRange] <;> rfl
end ContactOriginalLaurentOverlap318
