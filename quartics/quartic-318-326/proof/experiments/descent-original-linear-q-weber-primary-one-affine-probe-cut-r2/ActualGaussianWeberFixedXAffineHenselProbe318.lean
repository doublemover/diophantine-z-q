module
public import ActualGaussianWeberPowerSeriesArc318
import Mathlib.Algebra.Polynomial.Derivative
public section
noncomputable section

namespace ActualGaussianWeberFixedXAffineHenselProbe318

open IsLocalRing Polynomial ActualGaussianWeberPowerSeriesArc318

variable {k : Type*} [Field k]

private theorem parameter_const_zero : constantTerm k (parameter k) = 0 := by
  change PowerSeries.constantCoeff ((seriesEquiv k).symm ((seriesEquiv k) PowerSeries.X)) = 0
  rw [RingEquiv.symm_apply_apply,PowerSeries.constantCoeff_X]

/-- At an ordinary affine point with nonzero ordinate, choose the
actual abscissa x+t, not an unspecified residue-field lift. It
is visibly nonconstant; the Hensel lift is only in the ordinate. -/
theorem fixed_x_lift (h2 : (2:k) ≠ 0) (x y : k) (hy : y ≠ 0)
    (he : y^2 = x^3-x) :
    let X := constVal k x + parameter k
    ∃ Y : FormalValuation k, Y^2 = X^3-X ∧
      constantTerm k X = x ∧ constantTerm k Y = y ∧
      X ≠ constVal k (constantTerm k X) := by
  let V := FormalValuation k
  letI : HenselianLocalRing V := formal_henselian k
  let X := constVal k x + parameter k
  let B := constVal k y
  let f : V[X] := Polynomial.X^2-C (X^3-X)
  have hx : constantTerm k X = x := by
    change constantTerm k (constVal k x + parameter k) = x
    rw [map_add,constantTerm_const,parameter_const_zero,add_zero]
  have hNon : X ≠ constVal k (constantTerm k X) := by
    intro h
    have h' : constVal k x + parameter k = constVal k x + 0 := by
      change X = constVal k x + 0
      rw [add_zero,← hx]
      exact h
    exact parameter_ne k (add_left_cancel h')
  have hcompat (w : V) : residueFormal k (residue V w) = constantTerm k w := by
    change ResidueField.lift (constantTerm k) (residue V w) = constantTerm k w
    exact ResidueField.lift_residue_apply _ _
  have hf : f.Monic := monic_X_pow_sub_C _ (by decide)
  have h0 : f.eval B ∈ maximalIdeal V := (residue_eq_zero_iff _).mp (by
    apply (residueFormal k).injective
    rw [hcompat,map_zero]
    simp only [f,eval_sub,eval_pow,eval_X,eval_C,map_pow,map_sub,hx,B,constantTerm_const]
    exact sub_eq_zero.mpr he)
  have hDer : f.derivative.eval B = (2:V)*B := by
    change ((Polynomial.X^2-C (X^3-X):V[X]).derivative).eval B = _
    rw [derivative_sub,derivative_C,derivative_X_pow,sub_zero]
    simp only [show (2:ℕ)-1=1 by decide,pow_one,eval_mul,eval_C,eval_ofNat,
      eval_natCast,eval_X,Nat.cast_ofNat]
  have h1 : IsUnit (f.derivative.eval B) := (residue_ne_zero_iff_isUnit _).mp (by
    intro h
    have e := congrArg (residueFormal k) h
    rw [hcompat,map_zero,hDer,map_mul,map_ofNat] at e
    change (2:k)*constantTerm k (constVal k y)=0 at e
    rw [constantTerm_const] at e
    exact (mul_ne_zero h2 hy) e)
  obtain ⟨Y,hY,hYB⟩ := HenselianLocalRing.is_henselian f hf B h0 h1
  have hEq : Y^2=X^3-X := by
    apply sub_eq_zero.mp
    simpa only [f,eval_sub,eval_pow,eval_X,eval_C] using (IsRoot.def.mp hY)
  have hY0 : constantTerm k Y = y := by
    have h := congrArg (residueFormal k) ((residue_eq_zero_iff (Y-B)).mpr hYB)
    rw [hcompat,map_zero,map_sub] at h
    exact (sub_eq_zero.mp h).trans (constantTerm_const k y)
  exact ⟨Y,hEq,hx,hY0,hNon⟩

end ActualGaussianWeberFixedXAffineHenselProbe318
