module
public import CompactLocalPointCoding318
public import CoherentMultipleCharts318
public import ShortCurveBaseChange318
public section
noncomputable section
namespace FormalPoleCoherentChart318
open ReciprocalDouble318 WeierstrassCurve.Affine
open LocalDerivativeSeparation318
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [CharZero F]
variable (w : AbsoluteValue F ℝ) (hna : IsNonarchimedean w)

include hna in
/-- An actual affine pole goes to the positive identity branch of the
historical duplication chart. Both coordinates are evaluated as the original
rational expressions; no sign choice or square-root selection is introduced. -/
theorem pole_chart (D x y : F) (hD : w D≤1) (hx : 1<w x)
    (hc : y^2=x^3-D*x) :
    w (2*y/(x^2+D))<1 ∧
    w ((x^4-6*D*x^2+D^2)/(x^2+D)^2-1)<1 := by
  have hxp : 0<w x := lt_trans zero_lt_one hx
  have hx2 : 1<(w x)^2 := by nlinarith
  have hden : w (x^2+D)=(w x)^2 := by
    have he := hna.add_eq_left_of_lt (map_neg_eq_map w)
      (show w D<w (x^2) by rw [map_pow]; exact hD.trans_lt hx2)
    simpa only [map_pow] using he
  have hden0 : x^2+D≠0 := w.pos_iff.mp (by rw [hden]; positivity)
  have hy : (w y)^2=(w x)^3 := by
    have hsmall : w (-(D*x))<w (x^3) := by
      rw [map_neg_eq_map,map_mul,map_pow]
      have hmul := mul_le_of_le_one_left (apply_nonneg w x) hD
      have hpow : w x<(w x)^3 := by nlinarith [sq_nonneg (w x-1)]
      exact hmul.trans_lt hpow
    have he := congrArg w hc
    simpa only [map_pow,sub_eq_add_neg,hna.add_eq_left_of_lt (map_neg_eq_map w) hsmall] using he
  have h2 := nat_le_one w hna 2
  have h8 := nat_le_one w hna 8
  constructor
  · have hu : (w (2*y/(x^2+D)))^2=(w (2:F))^2/w x := by
      rw [map_div₀,map_mul,hden,mul_pow,div_pow,hy]
      field_simp [ne_of_gt hxp]
      ring
    have hb : (w (2:F))^2≤1 := by nlinarith [apply_nonneg w (2:F)]
    have ht : (w (2:F))^2/w x<1 := (div_lt_one hxp).mpr (hb.trans_lt hx)
    rw [←hu] at ht
    nlinarith [apply_nonneg w (2*y/(x^2+D))]
  · have he : (x^4-6*D*x^2+D^2)/(x^2+D)^2-1= -(8*D*x^2)/(x^2+D)^2 := by
      field_simp [hden0]
      ring
    rw [he,map_div₀,map_neg_eq_map,map_mul,map_mul,map_pow,map_pow,hden]
    have hbound : w (8:F)*w D≤1 := mul_le_one₀ h8 (apply_nonneg w D) hD
    have hr : w (8:F)*w D*(w x)^2/((w x)^2)^2=w (8:F)*w D/(w x)^2 := by
      field_simp [ne_of_gt hxp]
      ring
    rw [hr]
    exact (div_lt_one (sq_pos_of_pos hxp)).mpr (hbound.trans_lt hx2)

/-- The same conclusion on the original K-valued point, after any actual
field embedding. The formal subgroup may include zero; its original chart
is exactly (0,1), not the other point (0,−1). -/
theorem actual_chart {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    (φ : ConcreteG8Domain.K →+* L) (w : AbsoluteValue L ℝ)
    (hna : IsNonarchimedean w) (hD : w (φ ConcreteG8Domain.D)≤1)
    (Q : LocalGenerator318.E.Point)
    (hQ : ShortCurveBaseChange318.pointMap φ ConcreteG8Domain.D Q∈
      AlgebraicFormalSubgroup318.formalSubgroup w hna (φ ConcreteG8Domain.D) hD) :
    w (φ (CoherentMultipleCharts318.u Q))<1 ∧
    w (φ (CoherentMultipleCharts318.v Q-1))<1 := by
  cases Q with
  | zero => simp [CoherentMultipleCharts318.u,CoherentMultipleCharts318.v]
  | some x y h =>
    have hx : 1<w (φ x) := by
      rcases hQ with hz|hx
      · rw [ShortCurveBaseChange318.pointMap_some] at hz
        exact False.elim (Point.some_ne_zero _ hz)
      · simpa only [ShortCurveBaseChange318.pointMap_some,Point.xRep_some,Matrix.cons_val_zero] using hx
    have he := pole_chart w hna (φ ConcreteG8Domain.D) (φ x) (φ y) hD hx
      (by simpa only [map_pow,map_sub,map_mul] using
        congrArg φ (FormalChartDouble.ordinate_equation ConcreteG8Domain.D x y h))
    simpa only [CoherentMultipleCharts318.u,CoherentMultipleCharts318.v,
      map_div₀,map_sub,map_mul,map_add,map_pow,map_ofNat,map_one] using he

end FormalPoleCoherentChart318
