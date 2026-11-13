module
public import ContactPicardIsomOrbitUniversal318
public import ProperChartConstants318
public section
noncomputable section
namespace ContactOriginalRationalFunctionConstants318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ)
abbrev source := ContactGlobalSmooth318.Model c
abbrev projection := ContactIntrinsicDifferentials318.structureMap c
abbrev chart := SourceGlobalAffine318.chartEmbedding c
abbrev chartRing := ContactKummerOrder318.SourceOrder c
/-- Reuse the actual proper/geometric-integral constants argument for
EVERY original twist, not just the earlier fixed arithmetic twist. -/
lemma constants_bijective : Function.Bijective
    (ProperChartConstants318.structuralMap (projection c)) := by
  letI : IsIntegral (source c) := ContactProjectiveModel318.model_integral c
  letI : IsDomain (chartRing c) := ContactKummerOrder318.source_domain c
  letI : IsProper (projection c) := (ContactGlobalProper318.proper_integral_extension c).2.2
  letI : IsDomain (AlgebraicClosure ℚ ⊗[ℚ] chartRing c) :=
    SourceScalarExtension318.scalarExtension_domain (AlgebraicClosure ℚ) c
  exact ProperChartConstants318.constant_bijective (projection c) (chart c)
    (SourceGlobalAffine318.chartEmbedding_over_Q c)
lemma appTop_isIso : IsIso (projection c).appTop := by
  haveI : IsIso ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ (projection c).appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (constants_bijective c)
  exact (isIso_comp_left_iff _ _).mp inferInstance
end ContactOriginalRationalFunctionConstants318
