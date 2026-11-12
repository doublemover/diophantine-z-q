module
public import OriginalPeriodSchemePointGluing318
public section
noncomputable section
namespace OriginalPeriodGlobalSchemePoints318
open CategoryTheory AlgebraicGeometry
open OriginalPeriodProjectiveModel318 OriginalPeriodNativeChartGerms318
open OriginalPeriodSchemeChartPoints318 OriginalPeriodSchemePointGluing318
open ComplexAffineFreeTranslation318 Filter Topology
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

lemma infinity_evaluation_zero
    (hq : nativeV L 0-nativeU L 0^3-A L*nativeU L 0*nativeV L 0^2-B L*nativeV L 0^3=0) :
    infinityEvaluation L 0 hq=InfinityChart318.origin (A L) (B L) := by
  apply InfinityChart318.hom_ext
  · rw [infinity_x,nativeU_zero,InfinityChart318.origin_x]
  · rw [infinity_z,nativeV_zero,InfinityChart318.origin_z]
lemma infinityPoint_zero
    (hq : nativeV L 0-nativeU L 0^3-A L*nativeU L 0*nativeV L 0^2-B L*nativeV L 0^3=0) :
    infinityPoint L 0 hq=infinity L := by
  rw [infinityPoint,infinity_evaluation_zero]
  rfl

/-- Global original torus points as ACTUAL scheme-valued complex points.
The pole is the independent algebraic infinity section. -/
@[expose] def schemePoint (q : Torus L) : Spec (CommRingCat.of ℂ) ⟶ model L :=
  if hn:q=0 then infinity L else finitePoint L ⟨q,hn⟩
lemma schemePoint_zero : schemePoint L 0=infinity L := dif_pos rfl
lemma schemePoint_nonzero (q : Torus L) (hq : q≠0) :
    schemePoint L q=finitePoint L ⟨q,hq⟩ := dif_neg hq
lemma schemePoint_over_base (q : Torus L) : schemePoint L q ≫ structure L=𝟙 _ := by
  by_cases hq : q=0
  · subst q
    rw [schemePoint_zero]
    exact infinity_section L
  · rw [schemePoint_nonzero L q hq]
    exact finitePoint_over_base L ⟨q,hq⟩

/-- The global original scheme-point map is given by the genuine
holomorphic infinity coordinate-ring evaluations on a WHOLE original
neighborhood, INCLUDING the pole. The finite/infinity map identity has
been proved through actual localization gluing, not inferred from values. -/
theorem whole_pole_chart : ∀ᶠ q in 𝓝 (0:Torus L),
    ∃hq:nativeV L q-nativeU L q^3-A L*nativeU L q*nativeV L q^2-B L*nativeV L q^3=0,
      schemePoint L q=infinityPoint L q hq := by
  filter_upwards [infinity_equation L,original_neighborhood_gluing L] with q hq hg
  by_cases hn : q=0
  · subst q
    exact ⟨hq,(schemePoint_zero L).trans (infinityPoint_zero L hq).symm⟩
  · obtain ⟨he,hpoint⟩ := hg hn
    exact ⟨he,(schemePoint_nonzero L q hn).trans hpoint⟩
end OriginalPeriodGlobalSchemePoints318
