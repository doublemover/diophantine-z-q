module
public import IntrinsicChartNormalization318
public import IntrinsicChartSections318
public import ContactGlobalSmooth318
public section
noncomputable section
namespace ContactIntrinsicDifferentials318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

/-- The actual structural morphism of the smooth proper integral contact
normalization, not a detached affine or function-field model. -/
@[expose] def structureMap : ContactGlobalSmooth318.Model c ⟶ Spec (CommRingCat.of ℚ) :=
  (ContactProjectiveModel318.coverMap c).fromNormalization ≫ ProjectiveJLine318.structureMap ℚ

/-- Genuine relative differential sheaf on the actual complete source. -/
@[expose] def omega : (ContactGlobalSmooth318.Model c).Modules :=
  FamilyIntrinsicDifferentials318.omega (structureMap c)

@[expose] def derivation := FamilyIntrinsicDifferentials318.D (structureMap c)

/-- The intrinsic canonical differential object restricts to the ordinary
Kähler differential sheaf of the full actual contact t-chart. -/
@[expose] def sourceIso :
    AffineDifferentialSheaf318.differentialSheaf
      (R:=ℚ) (S:=ContactKummerOrder318.SourceOrder c) ≅
    (omega c).restrict (SourceGlobalAffine318.chartEmbedding c) :=
  IntrinsicChartNormalization318.iso (SourceGlobalAffine318.chartEmbedding c) (structureMap c)
    (SourceGlobalAffine318.chartEmbedding_over_Q c)

/-- The same intrinsic differential object restricts to the actual attached
infinity normalization chart, with its verified Q-structure map. -/
@[expose] def infinityIso :
    AffineDifferentialSheaf318.differentialSheaf
      (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c) ≅
    (omega c).restrict (InfinityGlobalScheme318.chartEmbedding c) :=
  IntrinsicChartNormalization318.iso (InfinityGlobalScheme318.chartEmbedding c) (structureMap c)
    (InfinityStructureSmooth318.chartEmbedding_over_Q c)

/-- Both comparisons refer to a proved cover of the entire proper source. -/
theorem comparison_cover :
    (SourceGlobalAffine318.chartEmbedding c).opensRange ⊔
      (InfinityGlobalScheme318.chartEmbedding c).opensRange = ⊤ :=
  ContactGlobalSmooth318.actual_charts_cover c

/-- Exact normalization on every algebraic universal differential of the
source t-chart, retaining the actual ambient intrinsic derivation. -/
theorem source_D (s : ContactKummerOrder318.SourceOrder c) :
    moduleSpecΓFunctor.map (sourceIso c).hom
      ((tilde.isoTop (R:=CommRingCat.of (ContactKummerOrder318.SourceOrder c))
        (ModuleCat.of _ (KaehlerDifferential ℚ (ContactKummerOrder318.SourceOrder c)))).hom
          (KaehlerDifferential.D ℚ (ContactKummerOrder318.SourceOrder c) s)) =
    (derivation c).d (((SourceGlobalAffine318.chartEmbedding c).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (ContactKummerOrder318.SourceOrder c))).inv s)) := by
  exact IntrinsicChartNormalization318.differential _ _
    (SourceGlobalAffine318.chartEmbedding_over_Q c) s

/-- Exact normalization on the actual infinity chart. -/
theorem infinity_D (s : InfinityGlobalChart318.InfinityOrder c) :
    moduleSpecΓFunctor.map (infinityIso c).hom
      ((tilde.isoTop (R:=CommRingCat.of (InfinityGlobalChart318.InfinityOrder c))
        (ModuleCat.of _ (KaehlerDifferential ℚ (InfinityGlobalChart318.InfinityOrder c)))).hom
          (KaehlerDifferential.D ℚ (InfinityGlobalChart318.InfinityOrder c) s)) =
    (derivation c).d (((InfinityGlobalScheme318.chartEmbedding c).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (InfinityGlobalChart318.InfinityOrder c))).inv s)) := by
  exact IntrinsicChartNormalization318.differential _ _
    (InfinityStructureSmooth318.chartEmbedding_over_Q c) s
end ContactIntrinsicDifferentials318
