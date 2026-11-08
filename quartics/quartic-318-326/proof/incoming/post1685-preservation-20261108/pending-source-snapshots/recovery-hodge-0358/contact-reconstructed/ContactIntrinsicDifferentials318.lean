module
public import IntrinsicChartNormalization318
public import ContactGlobalSmooth318
public section
noncomputable section
namespace ContactIntrinsicDifferentials318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

abbrev Model := ContactGlobalSmooth318.Model c
@[expose] def structureMap : Model c ⟶ Spec (CommRingCat.of ℚ) :=
  (ContactProjectiveModel318.coverMap c).fromNormalization ≫ ProjectiveJLine318.structureMap ℚ
@[expose] def omega : (Model c).Modules := FamilyIntrinsicDifferentials318.omega (structureMap c)
@[expose] def derivation := FamilyIntrinsicDifferentials318.D (structureMap c)

@[expose] def sourceIso :
    AffineDifferentialSheaf318.differentialSheaf (R:=ℚ) (S:=ContactKummerOrder318.SourceOrder c) ≅
      (omega c).restrict (SourceGlobalAffine318.chartEmbedding c) :=
  IntrinsicChartNormalization318.iso (SourceGlobalAffine318.chartEmbedding c)
    (structureMap c) (SourceGlobalAffine318.chartEmbedding_over_Q c)

@[expose] def infinityIso :
    AffineDifferentialSheaf318.differentialSheaf (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c) ≅
      (omega c).restrict (InfinityGlobalScheme318.chartEmbedding c) :=
  IntrinsicChartNormalization318.iso (InfinityGlobalScheme318.chartEmbedding c)
    (structureMap c) (InfinityStructureSmooth318.chartEmbedding_over_Q c)

theorem source_D (s : ContactKummerOrder318.SourceOrder c) :
    moduleSpecΓFunctor.map (sourceIso c).hom
      ((tilde.isoTop (R:=CommRingCat.of (ContactKummerOrder318.SourceOrder c))
        (ModuleCat.of (ContactKummerOrder318.SourceOrder c)
          (KaehlerDifferential ℚ (ContactKummerOrder318.SourceOrder c)))).hom
        (KaehlerDifferential.D ℚ (ContactKummerOrder318.SourceOrder c) s)) =
      (derivation c).d ((SourceGlobalAffine318.chartEmbedding c).appIso ⊤ |>.inv
        ((Scheme.ΓSpecIso (CommRingCat.of (ContactKummerOrder318.SourceOrder c))).inv s)) :=
  IntrinsicChartNormalization318.differential (SourceGlobalAffine318.chartEmbedding c)
    (structureMap c) (SourceGlobalAffine318.chartEmbedding_over_Q c) s

theorem infinity_D (s : InfinityGlobalChart318.InfinityOrder c) :
    moduleSpecΓFunctor.map (infinityIso c).hom
      ((tilde.isoTop (R:=CommRingCat.of (InfinityGlobalChart318.InfinityOrder c))
        (ModuleCat.of (InfinityGlobalChart318.InfinityOrder c)
          (KaehlerDifferential ℚ (InfinityGlobalChart318.InfinityOrder c)))).hom
        (KaehlerDifferential.D ℚ (InfinityGlobalChart318.InfinityOrder c) s)) =
      (derivation c).d ((InfinityGlobalScheme318.chartEmbedding c).appIso ⊤ |>.inv
        ((Scheme.ΓSpecIso (CommRingCat.of (InfinityGlobalChart318.InfinityOrder c))).inv s)) :=
  IntrinsicChartNormalization318.differential (InfinityGlobalScheme318.chartEmbedding c)
    (structureMap c) (InfinityStructureSmooth318.chartEmbedding_over_Q c) s

theorem comparison_cover :
    (SourceGlobalAffine318.chartEmbedding c).opensRange ⊔
      (InfinityGlobalScheme318.chartEmbedding c).opensRange = ⊤ :=
  ContactGlobalSmooth318.actual_charts_cover c
end ContactIntrinsicDifferentials318
