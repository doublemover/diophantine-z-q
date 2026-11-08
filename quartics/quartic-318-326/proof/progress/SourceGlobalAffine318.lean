module
public import SourceClosureComparison318
public import NormalitySpanDescent318
public import SourceBranchNormal318
public import SourceGlobalSmooth318
public import NormalizationBaseCompatibility318
public section
noncomputable section
namespace SourceGlobalAffine318
open CategoryTheory AlgebraicGeometry
open ContactKummerOrder318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
local instance sourceDomain : IsDomain (SourceOrder c):=source_domain c
local instance openAlgebra : Algebra R (OpenOrder c):=(ContactGlobalProper318.finitePolynomial c).toAlgebra

theorem source_integrallyClosed : IsIntegrallyClosed (SourceOrder c):=
  NormalitySpanDescent318.of_principal_cover (SourceDenominatorCover318.denominator c)
    (SourceDenominatorCover318.span_top c) (SourceBranchNormal318.localized_integrallyClosed c)

@[expose] def actualOpen : (ContactProjectiveModel318.coverMap c).normalization.affineOpens:=
  ⟨(ContactProjectiveModel318.coverMap c).fromNormalization⁻¹ᵁ(JLineAtlas318.chart ℚ 1 ''ᵁ ⊤),
    (NormalizationBaseCompatibility318.target_affine (JLineAtlas318.chart ℚ 1)).preimage _⟩
@[expose] def chartIso : Spec (CommRingCat.of (SourceOrder c))≅Spec (SourceClosureComparison318.chartRing c):=
  Scheme.Spec.mapIso (SourceClosureComparison318.actualChartEquiv c
    (source_integrallyClosed c)).toCommRingCatIso.op
@[expose] def chartEmbedding : Spec (CommRingCat.of (SourceOrder c))⟶
    (ContactProjectiveModel318.coverMap c).normalization:=
  (chartIso c).hom≫(actualOpen c).2.fromSpec
instance chartEmbedding_open : IsOpenImmersion (chartEmbedding c):=by
  unfold chartEmbedding
  infer_instance

theorem chartEmbedding_range : (chartEmbedding c).opensRange=(actualOpen c).1:=by
  change ((chartIso c).hom≫(actualOpen c).2.fromSpec).opensRange=_
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (actualOpen c).2.opensRange_fromSpec

theorem chartEmbedding_over_contact_line :
    chartEmbedding c≫(ContactProjectiveModel318.coverMap c).fromNormalization=
    Spec.map (CommRingCat.ofHom (algebraMap R (SourceOrder c)))≫JLineAtlas318.chart ℚ 1:=by
  exact NormalizationBaseCompatibility318.factored_chart_over_base
    (C:=CommRingCat.of (SourceOrder c))
    (CommRingCat.ofHom (ContactGlobalProper318.finitePolynomial c)) (JLineAtlas318.chart ℚ 1)
    (ContactProjectiveModel318.coverMap c) (ContactGlobalProper318.finite_factor c)
    (SourceClosureComparison318.sourceClosureEquiv c (source_integrallyClosed c))

theorem chartEmbedding_over_Q :
    chartEmbedding c≫(ContactProjectiveModel318.coverMap c).fromNormalization≫
      ProjectiveJLine318.structureMap ℚ=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (SourceOrder c))):=by
  rw [←Category.assoc,chartEmbedding_over_contact_line,Category.assoc,JLineAtlas318.chart_over_base,
    ←Spec.map_comp]
  congr 1

theorem actual_source_smooth : Smooth
    (chartEmbedding c≫(ContactProjectiveModel318.coverMap c).fromNormalization≫
      ProjectiveJLine318.structureMap ℚ):=by
  rw [chartEmbedding_over_Q]
  exact (HasRingHomProperty.Spec_iff (P:=@Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr (SourceGlobalSmooth318.source_smooth c))
end SourceGlobalAffine318
