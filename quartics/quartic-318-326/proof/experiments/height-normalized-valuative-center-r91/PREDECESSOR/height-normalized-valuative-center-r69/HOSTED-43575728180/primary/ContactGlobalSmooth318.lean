module
public import ContactSmoothBaseCover318
public import SourceGlobalAffine318
public import InfinityStructureSmooth318
public section
noncomputable section
namespace ContactGlobalSmooth318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
abbrev Model:Scheme:=(ContactProjectiveModel318.coverMap c).normalization

/-- The actual two normalization charts cover the entire global model. -/
theorem actual_charts_cover :
    (SourceGlobalAffine318.chartEmbedding c).opensRange⊔
      (InfinityGlobalScheme318.chartEmbedding c).opensRange=⊤:=by
  rw [SourceGlobalAffine318.chartEmbedding_range,InfinityGlobalScheme318.chartEmbedding_range]
  change (ContactProjectiveModel318.coverMap c).fromNormalization⁻¹ᵁ
      (JLineAtlas318.chart ℚ 1 ''ᵁ ⊤)⊔
    (ContactProjectiveModel318.coverMap c).fromNormalization⁻¹ᵁ
      (InfinityGlobalBase318.baseOpen c ''ᵁ ⊤)=⊤
  rw [Scheme.Hom.image_top_eq_opensRange,Scheme.Hom.image_top_eq_opensRange,
    ←Scheme.Hom.preimage_sup,ContactSmoothBaseCover318.base_cover,Scheme.Hom.preimage_top]

@[expose] def chart : Bool→Scheme
  | false=>Spec (CommRingCat.of (ContactKummerOrder318.SourceOrder c))
  | true=>ReciprocalInfinityNormalization318.neighborhood c
@[expose] def embedding : (b:Bool)→chart c b⟶Model c
  | false=>SourceGlobalAffine318.chartEmbedding c
  | true=>InfinityGlobalScheme318.chartEmbedding c
instance embedding_open (b:Bool) : IsOpenImmersion (embedding c b):=by
  cases b
  · exact SourceGlobalAffine318.chartEmbedding_open c
  · exact InfinityGlobalScheme318.chartEmbedding_open c

@[expose] def cover : (Model c).OpenCover where
  I₀:=Bool
  X:=chart c
  f:=embedding c
  mem₀:=by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,inferInstance⟩
    intro x
    have hx:x∈(SourceGlobalAffine318.chartEmbedding c).opensRange⊔
        (InfinityGlobalScheme318.chartEmbedding c).opensRange:=by
      rw [actual_charts_cover]
      trivial
    rcases hx with hx|hx
    · obtain ⟨p,hp⟩:=hx
      exact ⟨false,p,hp⟩
    · obtain ⟨p,hp⟩:=hx
      exact ⟨true,p,hp⟩

/-- Global smoothness of the actual proper normalization over Q, proved
using its actual source and infinity embeddings with their structure maps. -/
theorem model_smooth : Smooth
    ((ContactProjectiveModel318.coverMap c).fromNormalization≫ProjectiveJLine318.structureMap ℚ):=by
  apply IsZariskiLocalAtSource.of_openCover (P:=@Smooth) (cover c)
  intro b
  cases b
  · exact SourceGlobalAffine318.actual_source_smooth c
  · exact InfinityStructureSmooth318.actual_infinity_smooth c

/-- A genuine smooth proper integral Q-model of the original contact cover. -/
theorem smooth_proper_integral_model :
    Smooth (ContactProjectiveModel318.modelMap c≫ProjectiveJLine318.structureMap ℚ)∧
    IsProper (ContactProjectiveModel318.modelMap c≫ProjectiveJLine318.structureMap ℚ)∧
    IsIntegral (ContactProjectiveModel318.model c):=
  ⟨model_smooth c,(ContactGlobalProper318.proper_integral_extension c).2.2,
    (ContactGlobalProper318.proper_integral_extension c).2.1⟩
end ContactGlobalSmooth318
