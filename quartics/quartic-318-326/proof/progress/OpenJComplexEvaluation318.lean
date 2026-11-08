module
public import OpenJModel318
public import ModularWeierstrass318
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section
namespace OpenJComplexEvaluation318
set_option maxHeartbeats 0

/-- Exactly the complex points of the arithmetic j-line chart away from 0 and 1728. -/
@[expose] def Admissible (tau : UpperHalfPlane) : Prop :=
  ActualQJ318.jInvariant tau ≠ 0 ∧ ActualQJ318.jInvariant tau ≠ 1728

@[expose] def polynomialEval (tau : UpperHalfPlane) : Polynomial ℤ →+* ℂ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℂ) (ActualQJ318.jInvariant tau)

lemma denominator_isUnit (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : Admissible tau) : IsUnit (polynomialEval tau (OpenJModel318.denominator N)) := by
  apply isUnit_iff_ne_zero.mpr
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simpa [polynomialEval, OpenJModel318.denominator, sub_ne_zero] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (6:ℂ) ≠ 0) hN) h.1)
      (sub_ne_zero.mpr h.2)

/-- The actual localization morphism, not a freely assumed comparison map. -/
@[expose] def evaluation (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : Admissible tau) : OpenJModel318.Base N →+* ℂ :=
  IsLocalization.Away.lift (OpenJModel318.denominator N) (denominator_isUnit N tau h)

@[simp] theorem evaluation_jCoord (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : Admissible tau) : evaluation N tau h (OpenJModel318.jCoord N) =
      ActualQJ318.jInvariant tau := by
  simp [evaluation, OpenJModel318.jCoord, polynomialEval]

theorem evaluation_inverse (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : Admissible tau) : evaluation N tau h (OpenJModel318.inverseDenominator N) =
      (ActualQJ318.jInvariant tau - 1728)⁻¹ := by
  have he := congrArg (evaluation N tau h) (OpenJModel318.denominator_inverse N)
  simp only [map_mul, map_sub, map_ofNat, map_one, evaluation_jCoord] at he
  exact (inv_eq_of_mul_eq_one_right he).symm

@[expose] def fiber (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : Admissible tau) : WeierstrassCurve ℂ :=
  (OpenJModel318.integralModel N).map (evaluation N tau h)

instance fiber_isElliptic (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : Admissible tau) : (fiber N tau h).IsElliptic := inferInstanceAs
      (((OpenJModel318.integralModel N).map (evaluation N tau h)).IsElliptic)

theorem fiber_eq (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    fiber N tau h = OpenJModel318.curve (ActualQJ318.jInvariant tau)
      (ActualQJ318.jInvariant tau - 1728)⁻¹ := by
  ext <;> simp only [fiber, OpenJModel318.integralModel, OpenJModel318.curve,
    WeierstrassCurve.map, map_zero, map_mul, map_neg, map_ofNat,
    evaluation_jCoord, evaluation_inverse]

@[simp] theorem fiber_j (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : Admissible tau) : (fiber N tau h).j = ActualQJ318.jInvariant tau := by
  exact (OpenJModel318.base_change_j N (evaluation N tau h)).trans (evaluation_jCoord N tau h)

/-- The literal arithmetic fiber has an actual complex Weierstrass change of
variables to the genuine Eisenstein model; equality of j is proved above. -/
theorem exists_comparison (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : Admissible tau) : ∃ C : WeierstrassCurve.VariableChange ℂ,
      C • fiber N tau h = ModularWeierstrass318.curve tau := by
  apply WeierstrassCurve.exists_variableChange_of_j_eq
  rw [fiber_j, ModularWeierstrass318.curve_j]

end OpenJComplexEvaluation318
