module
public import ThreeJAnalyticGerms318
public section
noncomputable section
open Filter Topology
namespace ThreeJChartHolomorphy318
open AlgebraicGeometry CategoryTheory Polynomial
open ProjectiveLineFieldPoints318 ThreeProjectiveJCertificates318 ThreeAffineJMaps318
open ThreeProjectiveJPoints318 ThreeJAnalyticGerms318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma finite_numerator_formula (t : ℂ) (ht : finiteN t ≠ 0) :
    mapPoints (chartPoint (R:=ℚ) 1 t)=chartPoint (R:=ℚ) 0 (finitePole t) := by
  apply Subtype.ext
  change (Spec.map (CommRingCat.ofHom (aeval (R:=ℚ) t).toRingHom) ≫
    JLineAtlas318.chart ℚ 1) ≫ ThreeProjectiveJMap318.map = _
  rw [Category.assoc,ThreeProjectiveJMap318.finite_restriction]
  change Spec.map (CommRingCat.ofHom (aeval (R:=ℚ) t).toRingHom) ≫
    RationalPairGluing318.map finiteNumerator finiteDenominator finite_coprime = _
  have hn : aeval t finiteNumerator * (finiteN t)⁻¹=1 := by
    rw [(finite_evaluations t).1,mul_inv_cancel₀ ht]
  have he := RationalPairNumeratorEvaluation318.evaluation_formula _ _ finite_coprime
    (aeval (R:=ℚ) t) (finiteN t)⁻¹ hn
  simpa only [ProjectiveLineFieldPoints318.chartPoint,(finite_evaluations t).2,finitePole,div_eq_mul_inv] using he

lemma reciprocal_numerator_formula (s : ℂ) (hs : reciprocalN s ≠ 0) :
    mapPoints (chartPoint (R:=ℚ) 0 s)=chartPoint (R:=ℚ) 0 (reciprocalPole s) := by
  apply Subtype.ext
  change (Spec.map (CommRingCat.ofHom (aeval (R:=ℚ) s).toRingHom) ≫
    JLineAtlas318.chart ℚ 0) ≫ ThreeProjectiveJMap318.map = _
  rw [Category.assoc,ThreeProjectiveJMap318.reciprocal_restriction]
  change Spec.map (CommRingCat.ofHom (aeval (R:=ℚ) s).toRingHom) ≫
    RationalPairGluing318.map reciprocalNumerator reciprocalDenominator reciprocal_coprime = _
  have hn : aeval s reciprocalNumerator * (reciprocalN s)⁻¹=1 := by
    rw [(reciprocal_evaluations s).1,mul_inv_cancel₀ hs]
  have he := RationalPairNumeratorEvaluation318.evaluation_formula _ _ reciprocal_coprime
    (aeval (R:=ℚ) s) (reciprocalN s)⁻¹ hn
  simpa only [ProjectiveLineFieldPoints318.chartPoint,(reciprocal_evaluations s).2,reciprocalPole,div_eq_mul_inv] using he

lemma reciprocal_denominator_formula (s : ℂ) (hs : s ≠ 0) :
    mapPoints (chartPoint (R:=ℚ) 0 s)=chartPoint (R:=ℚ) 1 (reciprocalN s / s) := by
  apply Subtype.ext
  change (Spec.map (CommRingCat.ofHom (aeval (R:=ℚ) s).toRingHom) ≫
    JLineAtlas318.chart ℚ 0) ≫ ThreeProjectiveJMap318.map = _
  rw [Category.assoc,ThreeProjectiveJMap318.reciprocal_restriction]
  change Spec.map (CommRingCat.ofHom (aeval (R:=ℚ) s).toRingHom) ≫
    RationalPairGluing318.map reciprocalNumerator reciprocalDenominator reciprocal_coprime = _
  have hd : aeval s reciprocalDenominator * s⁻¹=1 := by
    rw [(reciprocal_evaluations s).2,mul_inv_cancel₀ hs]
  have he := RationalPairDenominatorEvaluation318.evaluation_formula _ _ reciprocal_coprime
    (aeval (R:=ℚ) s) s⁻¹ hd
  simpa only [ProjectiveLineFieldPoints318.chartPoint,(reciprocal_evaluations s).1,div_eq_mul_inv] using he

/-- An explicit analytic local representative in one of the two original
target evaluation charts, on a whole source-coordinate neighborhood. -/
@[expose] def HasAnalyticChartExpression (i : Fin 2) (t : ℂ) : Prop :=
  ∃ j : Fin 2, ∃ F : ℂ → ℂ, AnalyticAt ℂ F t ∧
    ∀ᶠ z in 𝓝 t, mapPoints (chartPoint (R:=ℚ) i z)=chartPoint (R:=ℚ) j (F z)

/-- Every finite source coordinate has an actual analytic scheme-map
representative, with numerator and denominator domains both covered. -/
theorem finite_chart_analytic (t : ℂ) : HasAnalyticChartExpression 1 t := by
  by_cases ht : t=0
  · subst t
    refine ⟨0,finitePole,finite_cusp_germ.1,?_⟩
    filter_upwards [(finiteN_analytic 0).continuousAt.eventually_ne finiteN_zero_ne] with z hz
    exact finite_numerator_formula z hz
  · refine ⟨1,(fun z => finiteN z/z^3),
      (finiteN_analytic t).div (analyticAt_id.pow 3) (pow_ne_zero 3 ht),?_⟩
    filter_upwards [eventually_ne_nhds ht] with z hz
    have hd : aeval z finiteDenominator ≠ 0 := by
      rw [(finite_evaluations z).2]
      exact pow_ne_zero 3 hz
    simpa only [(finite_evaluations z).1,(finite_evaluations z).2] using finite_formula z hd

/-- The reciprocal source chart is covered as well, including its origin. -/
theorem reciprocal_chart_analytic (s : ℂ) : HasAnalyticChartExpression 0 s := by
  by_cases hs : s=0
  · subst s
    refine ⟨0,reciprocalPole,reciprocal_cusp_germ.1,?_⟩
    filter_upwards [(reciprocalN_analytic 0).continuousAt.eventually_ne reciprocalN_zero_ne] with z hz
    exact reciprocal_numerator_formula z hz
  · refine ⟨1,(fun z => reciprocalN z/z),
      (reciprocalN_analytic s).div analyticAt_id hs,?_⟩
    filter_upwards [eventually_ne_nhds hs] with z hz
    exact reciprocal_denominator_formula z hz

/-- Exhaustive certificate on both original source charts. This statement
retains exact evaluation maps and neighborhood equalities, rather than merely
asserting that a rational formula is holomorphic away from its poles. -/
theorem all_chart_analytic (i : Fin 2) (t : ℂ) : HasAnalyticChartExpression i t := by
  fin_cases i
  · exact reciprocal_chart_analytic t
  · exact finite_chart_analytic t

/-- Every genuine scheme-valued point is covered by the local certificate.
Bundling these local expressions into ContMDiff is a separate API step. -/
theorem every_point_analytic (p : Points (R:=ℚ) (K:=ℂ)) :
    ∃ i : Fin 2, ∃ t : ℂ, chartPoint (R:=ℚ) i t=p ∧ HasAnalyticChartExpression i t := by
  obtain ⟨i,t,h⟩ := every_point_in_chart p
  exact ⟨i,t,h,all_chart_analytic i t⟩

/-- The ramification-order formulas belong to the exact scheme map: each
listed scalar is its reciprocal target expression on a full neighborhood. -/
theorem exact_cusp_germs :
    (∀ᶠ t in 𝓝 (0:ℂ), mapPoints (chartPoint (R:=ℚ) 1 t)=
      chartPoint (R:=ℚ) 0 (finitePole t)) ∧
    (∀ᶠ s in 𝓝 (0:ℂ), mapPoints (chartPoint (R:=ℚ) 0 s)=
      chartPoint (R:=ℚ) 0 (reciprocalPole s)) ∧
    AnalyticAt ℂ finitePole 0 ∧ meromorphicOrderAt finitePole 0=3 ∧
    AnalyticAt ℂ reciprocalPole 0 ∧ meromorphicOrderAt reciprocalPole 0=1 := by
  refine ⟨?_,?_,finite_cusp_germ.1,finite_cusp_germ.2.2,
    reciprocal_cusp_germ.1,reciprocal_cusp_germ.2.2⟩
  · filter_upwards [(finiteN_analytic 0).continuousAt.eventually_ne finiteN_zero_ne] with z hz
    exact finite_numerator_formula z hz
  · filter_upwards [(reciprocalN_analytic 0).continuousAt.eventually_ne reciprocalN_zero_ne] with z hz
    exact reciprocal_numerator_formula z hz

end ThreeJChartHolomorphy318
