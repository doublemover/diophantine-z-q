module
public import IntegralChartSectionDetection318
public import ContactGlobalSectionDetection318
public import IntrinsicChartNaturality318
public section
noncomputable section
namespace InfinityChartSectionExtension318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev X:=ContactGlobalSmooth318.Model c
abbrev I:=InfinityOpenChart318.OpenOrder c
abbrev O:=ContactKummerOrder318.OpenOrder c
abbrev M:(X c).Modules:=ContactIntrinsicDifferentials318.omega c
abbrev j:Spec (CommRingCat.of (I c))⟶X c:=InfinityGlobalScheme318.chartEmbedding c
abbrev k:Spec (CommRingCat.of (O c))⟶X c:=ContactOverlapIntrinsic318.embedding c
abbrev p:X c⟶Spec (CommRingCat.of ℚ):=ContactIntrinsicDifferentials318.structureMap c
local instance lift_open:IsOpenImmersion (Spec.map
    (CommRingCat.ofHom (ContactOverlapAlgebraMaps318.infinityMap c).toRingHom)):=
  ContactOverlapMaps318.infinityInclusion_open c
/-- Whole infinity-to-common naturality for the actual intrinsic sheaf. -/
theorem naturality (ω:KaehlerDifferential ℚ (I c)):
    (M c).presheaf.map (homOfLE (X:=(X c).Opens) (x:=k c ''ᵁ ⊤) (y:=j c ''ᵁ ⊤)
      (ContactInfinityTensorRestrictions318.infinityLE c)).op
      (IntrinsicChartSections318.sectionMap (Y:=X c) (R:=ℚ) (S:=I c) (j c) (p c)
        (InfinityStructureSmooth318.chartEmbedding_over_Q c) ω)=
    IntrinsicChartSections318.sectionMap (Y:=X c) (R:=ℚ) (S:=O c) (k c) (p c)
      (ContactOverlapIntrinsic318.over_Q c)
      (AlgHomDifferential318.map (R:=ℚ) (S:=I c) (T:=O c)
        (ContactOverlapAlgebraMaps318.infinityMap c) ω):=
  IntrinsicChartNaturality318.section_restrict_to
    (R:=ℚ) (S:=I c) (T:=O c) (ContactOverlapAlgebraMaps318.infinityMap c)
    (j c) (p c) (InfinityStructureSmooth318.chartEmbedding_over_Q c)
    (k c) (ContactOverlapIntrinsic318.over_Q c) (ContactOverlapMaps318.infinity_square c)
    (ContactInfinityTensorRestrictions318.infinityLE c) ω
lemma injective:Function.Injective ((M c).presheaf.map
    (homOfLE (X:=(X c).Opens) (x:=k c ''ᵁ ⊤) (y:=j c ''ᵁ ⊤)
      (ContactInfinityTensorRestrictions318.infinityLE c)).op):=by
  letI:IsIntegral (X c):=(ContactGlobalSmooth318.smooth_proper_integral_model c).2.2
  letI:Nonempty (k c ''ᵁ ⊤):=ContactGlobalSectionDetection318.common_nonempty c
  exact IntegralChartSectionDetection318.restrict_injective (M c) (j c)
    (ContactIntrinsicFrames318.infinityFrame c) (k c ''ᵁ ⊤)
    (ContactInfinityTensorRestrictions318.infinityLE c)
/-- Exact common equality extends to the entire infinity chart because the
actual intrinsic module has its genuine whole-chart unit frame. -/
@[expose] def section_eq (s:Γ(M c,⊤)) (ω:KaehlerDifferential ℚ (I c))
    (h:IntrinsicChartSections318.sectionMap (Y:=X c) (R:=ℚ) (S:=O c) (k c) (p c)
      (ContactOverlapIntrinsic318.over_Q c)
      (AlgHomDifferential318.map (R:=ℚ) (S:=I c) (T:=O c)
        (ContactOverlapAlgebraMaps318.infinityMap c) ω)=
      (M c).presheaf.map (homOfLE (X:=(X c).Opens) (x:=k c ''ᵁ ⊤)
        (show k c ''ᵁ ⊤≤(⊤:(X c).Opens) from le_top)).op s) :=
  IntegralChartSectionDetection318.global_local_eq (M c) (U:=j c ''ᵁ ⊤) (W:=k c ''ᵁ ⊤)
    (ContactInfinityTensorRestrictions318.infinityLE c) (injective c) s
    (IntrinsicChartSections318.sectionMap (Y:=X c) (R:=ℚ) (S:=I c) (j c) (p c)
      (InfinityStructureSmooth318.chartEmbedding_over_Q c) ω)
    (h.symm.trans (naturality c ω).symm)
end InfinityChartSectionExtension318
