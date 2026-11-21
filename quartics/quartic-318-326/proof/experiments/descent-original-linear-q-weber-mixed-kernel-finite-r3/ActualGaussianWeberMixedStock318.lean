module
public import ActualGaussianWeberMixedValuedData318
public import ActualGaussianWeberValuedKernelChart318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import all Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public section
noncomputable section

namespace ActualGaussianWeberMixedStock318

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

/-- The actual finite reduction read through its integral coordinates.
The membership proofs inside the stock constructor are not reindexed by rw. -/
theorem reduction_through_coordinates (h2 : (2:ResidueField V) ≠ 0)
    {x y : F} (hn : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) x y) (a b : V)
    (hx : x=V.subtype a) (hy : y=V.subtype b) :
    ∃ h : WeierstrassCurve.Affine.Nonsingular ((curve (ResidueField V)).toAffine) (residue V a) (residue V b),
      specialize V h2 (Point.some x y hn)=Point.some (residue V a) (residue V b) h := by
  subst x
  subst y
  classical
  have hQ := (literal_equation _ _).mp hn.1
  have hV := equation_in_subring V a b hQ
  refine ⟨nonsing_of_equation h2 (equation_in_residue V a b hV),?_⟩
  have ha : V.subtype a ∈ V := a.property
  have ea : (⟨V.subtype a,ha⟩ : V)=a := Subtype.ext rfl
  have eb : (⟨V.subtype b,integral_y V hQ ha⟩ : V)=b := Subtype.ext rfl
  simp only [specialize,dif_pos ha,finiteReduction]
  exact transport_some (congrArg (residue V) ea) (congrArg (residue V) eb)

variable [DecidableEq F]

/-- Exact affine-coordinate comparison and reduction for actual
O-kernel plus finite stock addition at the original place. -/
theorem mixed_kernel_finite (h2 : (2:ResidueField V) ≠ 0)
    (P : WP F) (a b : V)
    (hQ : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) (V.subtype a) (V.subtype b))
    (hP : specialize V h2 P=Point.zero) :
    specialize V h2 (P+Point.some _ _ hQ)=specialize V h2 (Point.some _ _ hQ) := by
  cases P with
  | zero =>
    have h : (Point.zero:WP F)+Point.some (V.subtype a) (V.subtype b) hQ =
        Point.some (V.subtype a) (V.subtype b) hQ := zero_add _
    rw [h]
  | some x y hn =>
    have hx := (specialize_some_eq_zero V h2 hn).mp hP
    have hx0 : x ≠ 0 := by
      intro H0
      exact hx (by simpa only [H0] using V.zero_mem)
    have hy0 := y_ne_of_nonintegral V hx ((literal_equation x y).mp hn.1)
    obtain ⟨T⟩ := from_nonintegral V hx hn
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
      simp only [H,map_add,map_sub,map_mul,map_one,map_pow,map_ofNat]
    have hX : X=A+t*u*beta^2*H t w A B := by
      change V.subtype K.X = _
      rw [K.x_formula,map_add]
      simp only [map_pow,map_mul,hH]
    have hY : Y= -B+(1+B*w)*u*beta^3*H t w A B := by
      change V.subtype K.Y = _
      rw [K.y_formula]
      simp only [map_add,map_neg,map_pow,map_mul,map_one,hH]
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
    rw [Point.add_of_X_ne hnAB]
    obtain ⟨v₁,h₁⟩ := reduction_through_coordinates V h2
      (nonsingular_add hn hQ (fun h => hnAB h.1)) K.X K.Y hAddX hAddY
    obtain ⟨v₂,h₂⟩ := reduction_through_coordinates V h2 hQ a b rfl rfl
    rw [h₁,h₂]
    exact transport_some K.x_residue K.y_residue

end ActualGaussianWeberMixedStock318
