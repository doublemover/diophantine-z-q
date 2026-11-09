module
public import ThreeProjectiveJMap318
public import RationalPairNumeratorEvaluation318
public import ProjectiveLineFieldPoints318
public import ActualThreeJChartConsumer318
public section
noncomputable section
namespace ThreeProjectiveJPoints318
open AlgebraicGeometry CategoryTheory Polynomial
open ProjectiveLineFieldPoints318 ThreeProjectiveJCertificates318 ThreeAffineJMaps318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The action of the exact glued Q scheme morphism on genuine base-preserving
complex scheme points. Its value is composition of morphisms, not a formula
chosen independently on a projective tuple. -/
@[expose] def mapPoints (p : Points (R:=ℚ) (K:=ℂ)) : Points (R:=ℚ) (K:=ℂ) :=
  ⟨p.val ≫ ThreeProjectiveJMap318.map,by
    rw [Category.assoc,ThreeProjectiveJMap318.over_Q]
    exact p.property⟩

/-- Finite source points with nonzero denominator use the actual finite target
chart. The nonvanishing hypothesis is retained, including at elliptic points. -/
theorem finite_formula (t : ℂ) (ht : aeval t finiteDenominator ≠ 0) :
    mapPoints (chartPoint (R:=ℚ) 1 t) =
      chartPoint (R:=ℚ) 1 (aeval t finiteNumerator / aeval t finiteDenominator) := by
  apply Subtype.ext
  change (Spec.map (CommRingCat.ofHom (aeval (R:=ℚ) t).toRingHom) ≫
    JLineAtlas318.chart ℚ 1) ≫ ThreeProjectiveJMap318.map = _
  rw [Category.assoc,ThreeProjectiveJMap318.finite_restriction]
  change Spec.map (CommRingCat.ofHom (aeval (R:=ℚ) t).toRingHom) ≫
    RationalPairGluing318.map finiteNumerator finiteDenominator finite_coprime = _
  simpa only [div_eq_mul_inv] using
    RationalPairDenominatorEvaluation318.evaluation_formula _ _ finite_coprime
      (aeval (R:=ℚ) t) (aeval t finiteDenominator)⁻¹ (mul_inv_cancel₀ ht)

/-- The finite source origin maps to actual target infinity. This is proved
through D(numerator), not by totalizing the finite rational quotient at zero. -/
theorem finite_zero :
    mapPoints (chartPoint (R:=ℚ) 1 (0:ℂ)) = chartPoint (R:=ℚ) 0 (0:ℂ) := by
  apply Subtype.ext
  change (Spec.map (CommRingCat.ofHom (aeval (R:=ℚ) (0:ℂ)).toRingHom) ≫
    JLineAtlas318.chart ℚ 1) ≫ ThreeProjectiveJMap318.map = _
  rw [Category.assoc,ThreeProjectiveJMap318.finite_restriction]
  change Spec.map (CommRingCat.ofHom (aeval (R:=ℚ) (0:ℂ)).toRingHom) ≫
    RationalPairGluing318.map finiteNumerator finiteDenominator finite_coprime = _
  have hn : aeval (0:ℂ) finiteNumerator ≠ 0 := by
    rw [ActualThreeJChartConsumer318.boundary_chart_values.1]
    norm_num
  have he := RationalPairNumeratorEvaluation318.evaluation_formula _ _ finite_coprime
    (aeval (R:=ℚ) (0:ℂ)) (aeval (0:ℂ) finiteNumerator)⁻¹ (mul_inv_cancel₀ hn)
  simpa only [ActualThreeJChartConsumer318.boundary_chart_values.2.1,zero_mul] using he

/-- The reciprocal source origin also maps to actual target infinity. -/
theorem reciprocal_zero :
    mapPoints (chartPoint (R:=ℚ) 0 (0:ℂ)) = chartPoint (R:=ℚ) 0 (0:ℂ) := by
  apply Subtype.ext
  change (Spec.map (CommRingCat.ofHom (aeval (R:=ℚ) (0:ℂ)).toRingHom) ≫
    JLineAtlas318.chart ℚ 0) ≫ ThreeProjectiveJMap318.map = _
  rw [Category.assoc,ThreeProjectiveJMap318.reciprocal_restriction]
  change Spec.map (CommRingCat.ofHom (aeval (R:=ℚ) (0:ℂ)).toRingHom) ≫
    RationalPairGluing318.map reciprocalNumerator reciprocalDenominator reciprocal_coprime = _
  have hn : aeval (0:ℂ) reciprocalNumerator * (1:ℂ)=1 := by
    rw [ActualThreeJChartConsumer318.boundary_chart_values.2.2.1,one_mul]
  have he := RationalPairNumeratorEvaluation318.evaluation_formula _ _ reciprocal_coprime
    (aeval (R:=ℚ) (0:ℂ)) (1:ℂ) hn
  simpa only [ActualThreeJChartConsumer318.boundary_chart_values.2.2.2,zero_mul] using he

end ThreeProjectiveJPoints318
