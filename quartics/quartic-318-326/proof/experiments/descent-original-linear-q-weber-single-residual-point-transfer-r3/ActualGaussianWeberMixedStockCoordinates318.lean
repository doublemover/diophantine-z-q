module
public import ActualGaussianWeberMixedValuedData318
public import ActualGaussianWeberValuedKernelChart318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import all Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public section
noncomputable section

namespace ActualGaussianWeberMixedStockCoordinates318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianChart318 ActualGaussianWeberHenselianPointMap318
open ActualGaussianWeberValuedKernelChart318
open ActualGaussianWeberMixedPolynomial318 ActualGaussianWeberMixedValuedData318

variable {F : Type*} [Field F] (V : ValuationSubring F)


private theorem transport_some {K : Type*} [CommRing K] {x y x' y' : K}
    {h : (curve K).toAffine.Nonsingular x y}
    {h' : (curve K).toAffine.Nonsingular x' y'} (hx : x=x') (hy : y=y') :
    Point.some x y h=Point.some x' y' h' := by
  subst x'
  subst y'
  rfl

variable [DecidableEq F]

/-- The exact green mixed stock proof also computes both integral
coordinates before reducing them. This refinement keeps the very
same integral chart and records the lift, not just its residue. -/
theorem mixed_stock_coordinates (h2 : (2:ResidueField V) ≠ 0)
    (P : WP F) (a b : V)
    (hQ : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) (V.subtype a) (V.subtype b))
    (hP : specialize V h2 P=Point.zero) (hNonzero : P≠Point.zero)
    (T : OriginData V P) :
    ∃ K : IntegralData V T.t T.w a b,
      ∃ h : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine)
          (V.subtype K.X) (V.subtype K.Y),
        P+Point.some (V.subtype a) (V.subtype b) hQ =
          Point.some (V.subtype K.X) (V.subtype K.Y) h := by
  cases P with
  | zero => exact (hNonzero rfl).elim
  | some x y hn =>
    have hx := (specialize_some_eq_zero V h2 hn).mp hP
    have hx0 : x ≠ 0 := by
      intro H0
      exact hx (by simpa only [H0] using V.zero_mem)
    have hy0 := y_ne_of_nonintegral V hx ((literal_equation x y).mp hn.1)
    obtain ⟨K⟩ := integral_data V a b T.smallT T.smallW T.chart
    let A := V.subtype a
    let B := V.subtype b
    let t := V.subtype T.t
    let w := V.subtype T.w
    let u := V.subtype K.u
    let beta := V.subtype K.beta
    let X := V.subtype K.X
    let Y := V.subtype K.Y
    let ell := WeierstrassCurve.Affine.slope ((curve F).toAffine) x A y B
    have hnAB : x≠A := fun H0 => hx (H0.symm ▸ a.property)
    have htn : t≠0 := by
      have ht : t= -x/y := T.t_exact
      rw [ht]
      exact div_ne_zero (neg_ne_zero.mpr hx0) hy0
    have ht : t= -x/y := T.t_exact
    have hw0 : w= -1/y := T.w_exact
    have hw : w≠0 := by
      rw [hw0]
      exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) hy0
    have ex : x=t/w := by rw [ht,hw0]; field_simp [hy0] <;> ring
    have ey : y= -1/w := by rw [hw0]; field_simp [hy0] <;> ring
    have hChart : identityChart t w := by
      have h := T.chart
      unfold identityChart at h ⊢
      simpa only [map_add,map_mul,map_pow] using congrArg V.subtype h
    have hEqQ : B^2=A^3-A := (literal_equation _ _).mp hQ.1
    have hwu : w=t^3*u := by
      simpa only [map_pow,map_mul] using congrArg V.subtype K.w_relation
    have hDen : (t-A*w)*beta=t := by
      simpa only [map_sub,map_mul] using congrArg V.subtype K.denominator
    obtain ⟨hd,hSquare,hShift⟩ := scaled_chord hChart hEqQ htn hw hwu hDen
    have hxD : t/w-A≠0 := sub_ne_zero.mpr (by simpa only [←ex] using hnAB)
    have hSlope : ell= -(1+B*w)/(t-A*w) := by
      change WeierstrassCurve.Affine.slope ((curve F).toAffine) x A y B= _
      rw [slope_of_X_ne hnAB,ex,ey]
      apply (div_eq_div_iff hxD hd).mpr
      field_simp [hw] <;> ring
    have hLine : ell*(x-A)=y-B := by
      change WeierstrassCurve.Affine.slope ((curve F).toAffine) x A y B*(x-A)=y-B
      rw [slope_of_X_ne hnAB]
      exact div_mul_cancel₀ _ (sub_ne_zero.mpr hnAB)
    have hH : V.subtype (H T.t T.w a b)=H t w A B := by
      simp only [H,map_add,map_sub,map_mul,map_one,map_pow,map_ofNat] <;> rfl
    have hX : X=A+t*u*beta^2*H t w A B := by
      change V.subtype K.X = _
      rw [K.x_formula,map_add]
      simp only [map_pow,map_mul,hH] <;> rfl
    have hY : Y= -B+(1+B*w)*u*beta^3*H t w A B := by
      change V.subtype K.Y = _
      rw [K.y_formula]
      simp only [map_add,map_neg,map_pow,map_mul,map_one,hH] <;> rfl
    have hAddX : WeierstrassCurve.Affine.addX ((curve F).toAffine) x A ell=X := by
      have ha : WeierstrassCurve.Affine.addX ((curve F).toAffine) x A ell=ell^2-x-A := by simp [addX,curve,toAffine]
      rw [ha,hSlope,ex,hX]
      linear_combination hSquare
    have hDif : X-A=t*u*beta^2*H t w A B := by rw [hX]; ring
    have hAddY : WeierstrassCurve.Affine.addY ((curve F).toAffine) x A y ell=Y := by
      have hs : WeierstrassCurve.Affine.addY ((curve F).toAffine) x A y ell= -B-ell*(X-A) := by
        have hn (a b : F) : WeierstrassCurve.Affine.negY ((curve F).toAffine) a b= -b := by simp [negY,curve,toAffine]
        rw [addY,hn,negAddY,hAddX]
        linear_combination hLine
      rw [hs,hDif,hY]
      calc
        _ = -B + ((1+B*w)/(t-A*w))*(t*u*beta^2*H t w A B) := by
          rw [hSlope,neg_div,neg_mul,sub_neg_eq_add]
        _ = _ := by rw [hShift]
    have hOut : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine)
        (V.subtype K.X) (V.subtype K.Y) := by
      change WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) X Y
      rw [←hAddX,←hAddY]
      exact nonsingular_add hn hQ (fun h => hnAB h.1)
    refine ⟨K,hOut,?_⟩
    rw [Point.add_of_X_ne hnAB]
    exact transport_some hAddX hAddY

end ActualGaussianWeberMixedStockCoordinates318
