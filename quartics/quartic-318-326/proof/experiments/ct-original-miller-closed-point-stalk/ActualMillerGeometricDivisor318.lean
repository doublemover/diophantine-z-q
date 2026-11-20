module
public import ActualMillerAffineValuation318
public import ActualMillerInfinityNormalization318
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Abel
import all ActualMillerInfinityNormalization318
import all ActualMillerInfinityChartMap318
import all ActualTwoDescentInfinityNativeFractionFunctions318
import all ActualTwoDescentInfinityLocalParameter318
public section
noncomputable section

namespace ActualMillerGeometricDivisor318

open ActualTwoDescentEllipticModel318 ActualTwoDescentAffineChartCoordinates318
open ActualTwoDescentOriginalFunctionFieldTheta318
open ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
open ActualTwoDescentOriginalGlobalInfinityPoleUnit318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityNativeDVR318 ActualTwoDescentInfinityNativeFractionFunctions318
open ActualTwoDescentInfinityNativeDomain318
open ActualMillerInfinityNormalization318 ActualMillerAffineLocalChart318 ActualMillerAffineValuation318

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- The same normalized meromorphic step, on every actual point pair. -/
def millerFunction (n : K) : Point n → Point n → OriginalFunctionField n
  | .zero, _ => 1
  | .some _ _ _, .zero => 1
  | .some x₁ y₁ _, .some x₂ y₂ _ =>
    if x₁ = x₂ ∧ y₁ = (curve n).toAffine.negY x₂ y₂ then rootFunction n x₁
    else
      let a := (curve n).toAffine.slope x₁ x₂ y₁ y₂
      nonverticalFunction n x₁ y₁ a ((curve n).toAffine.addX x₁ x₂ a)

/-- Finite divisor coefficients on actual geometric points, not a
scheme-theoretic principal divisor on all closed points. -/
def geometricDivisor (n : K) (P Q : Point n) : Point n →₀ ℤ :=
  Finsupp.single P 1 + Finsupp.single Q 1 -
    Finsupp.single (P + Q) 1 - Finsupp.single 0 1

abbrev originT (n : K) : InfinityFractionField n := -chartFieldMap n (chartU n)

/-- Each exponent is certified in the fraction field of the actual local
DVR by an actual unit times a uniformizer power. At O the uniformizer
is the fixed t=-X/Y from the normalized infinity certificate. -/
def HasGeometricOrder (n : K) (f : OriginalFunctionField n) : Point n → ℤ → Prop
  | .zero, k =>
    ∃ e : (InfinityLocalRing n)ˣ,
      originalNativeFunctionFieldEquiv n f =
        infinityFractionMap n (e : InfinityLocalRing n) * (originT n)^k
  | .some u v hR, k =>
    ∃ π : AffineLocal n u v hR.left, Irreducible π ∧
      ∃ e : (AffineLocal n u v hR.left)ˣ,
        localFieldEquiv n u v hR.left f =
          toLocalField n u v hR.left (e : AffineLocal n u v hR.left) *
          (toLocalField n u v hR.left π)^k

theorem origin_parameter_span (n : K) :
    IsLocalRing.maximalIdeal (InfinityLocalRing n) = Ideal.span {-localU n} := by
  rw [Ideal.span_singleton_neg]
  exact ActualTwoDescentInfinityMaximalGenerator318.actual_infinity_maximal_principal n

theorem origin_parameter_irreducible (n : K) : Irreducible (-localU n) :=
  actual_signed_parameter_uniformizer n

/-- The complement of the actual punctured infinity chart is the origin,
even when it is described as a prime ideal rather than a point. -/
theorem infinity_prime_off_overlap (n : K) (J : Ideal (InfinityChart n)) [J.IsPrime]
    (hv : chartV n ∈ J) : J = originIdeal n := by
  have hu3 : chartU n ^ 3 ∈ J := by
    rw [← actual_chart_cubic_relation n]
    exact J.mul_mem_right _ hv
  have hu : chartU n ∈ J := (inferInstance : J.IsPrime).mem_of_pow_mem 3 hu3
  have hle : originIdeal n ≤ J := by
    rw [ActualTwoDescentInfinityMaximalGenerator318.actual_origin_ideal_generators n]
    apply Ideal.span_le.mpr
    intro r hr
    rcases Set.mem_insert_iff.mp hr with rfl | hr
    · exact hu
    · rcases Set.mem_singleton_iff.mp hr with rfl
      exact hv
  exact ((originIdealMaximal n).eq_of_le
    (Ideal.IsPrime.ne_top (inferInstance : J.IsPrime)) hle).symm

private theorem originT_ne_zero (n : K) : originT n ≠ 0 :=
  neg_ne_zero.mpr (actual_infinity_fraction_u_nonzero n)

private theorem nonvertical_origin_order (n x y a z : K) :
    HasGeometricOrder n (nonverticalFunction n x y a z) 0 (-1) := by
  obtain ⟨e, he, _⟩ := actual_nonvertical_miller_origin_unit n x y a z
  refine ⟨e, ?_⟩
  change originalNativeFunctionFieldEquiv n (nonverticalFunction n x y a z) =
    infinityFractionMap n (e : InfinityLocalRing n) * (originT n)^(-1 : ℤ)
  rw [zpow_neg_one, ← div_eq_mul_inv]
  apply (eq_div_iff (originT_ne_zero n)).mpr
  simpa only [map_neg, mul_comm] using he

private theorem vertical_origin_order (n x : K) :
    HasGeometricOrder n (rootFunction n x) 0 (-2) := by
  obtain ⟨e, he, _⟩ := actual_vertical_miller_origin_unit n x
  refine ⟨e, ?_⟩
  change originalNativeFunctionFieldEquiv n (rootFunction n x) =
    infinityFractionMap n (e : InfinityLocalRing n) * (originT n)^(-((2 : ℕ) : ℤ))
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  apply (eq_div_iff (pow_ne_zero _ (originT_ne_zero n))).mpr
  simpa only [map_neg, mul_comm] using he

private theorem one_order (n : K) (hn : n ≠ 0) (R : Point n) :
    HasGeometricOrder n 1 R 0 := by
  cases R with
  | zero =>
    refine ⟨1, ?_⟩
    simp only [map_one, Units.val_one, zpow_zero, mul_one]
  | some u v hR =>
    letI := actual_affine_local_DVR n u v hn hR.left
    obtain ⟨π, hπ, hJ⟩ := actual_affine_local_principal n u v hn hR.left
    refine ⟨π, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπ hJ, 1, ?_⟩
    simp only [map_one, Units.val_one, zpow_zero, mul_one]

private theorem single_affine (n x y u v : K)
    (hP : (curve n).toAffine.Nonsingular x y) (hR : (curve n).toAffine.Nonsingular u v) :
    Finsupp.single (.some x y hP : Point n) (1 : ℤ) (.some u v hR) =
      (pointMultiplicity u v x y : ℤ) := by
  rw [Finsupp.single_apply]
  by_cases h : x = u ∧ y = v
  · have hp : (.some x y hP : Point n) = .some u v hR := by
      simpa only [WeierstrassCurve.Affine.Point.some.injEq] using h
    simp only [if_pos hp, pointMultiplicity, if_pos h, Nat.cast_one]
  · have hp : (.some x y hP : Point n) ≠ .some u v hR := by
      intro he
      exact h (by simpa only [WeierstrassCurve.Affine.Point.some.injEq] using he)
    simp only [if_neg hp, pointMultiplicity, if_neg h, Nat.cast_zero]

private theorem divisor_zero_left (n : K) (P : Point n) : geometricDivisor n 0 P = 0 := by
  simp only [geometricDivisor, zero_add] <;> abel

private theorem divisor_zero_right (n : K) (P : Point n) : geometricDivisor n P 0 = 0 := by
  simp only [geometricDivisor, add_zero] <;> abel

/-- Actual local order agreement at EVERY geometric point for the
literal secant/tangent step, also for collisions, inverse points,
and either input O. This is not an all-closed-point divisor API. -/
theorem geometric_divisor_agrees (n : K) (hn : n ≠ 0) (P Q R : Point n) :
    HasGeometricOrder n (millerFunction n P Q) R (geometricDivisor n P Q R) := by
  cases P with
  | zero =>
    change HasGeometricOrder n (millerFunction n 0 Q) R (geometricDivisor n 0 Q R)
    simpa only [millerFunction, divisor_zero_left, Finsupp.zero_apply] using one_order n hn R
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      simpa only [millerFunction, divisor_zero_right, Finsupp.zero_apply] using one_order n hn R
    | some x₂ y₂ h₂ =>
      let P : Point n := .some x₁ y₁ h₁
      let Q : Point n := .some x₂ y₂ h₂
      have hP : P ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero h₁
      have hQ : Q ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero h₂
      change HasGeometricOrder n (millerFunction n P Q) R (geometricDivisor n P Q R)
      by_cases hV : x₁ = x₂ ∧ y₁ = (curve n).toAffine.negY x₂ y₂
      · have hf : millerFunction n P Q = rootFunction n x₁ := by
          simp only [P, Q, millerFunction, if_pos hV]
        have hsum : P + Q = 0 := WeierstrassCurve.Affine.Point.add_of_Y_eq hV.1 hV.2
        rw [hf]
        cases R with
        | zero =>
          have hk : geometricDivisor n P Q 0 = -2 := by
            simp only [geometricDivisor, hsum, Finsupp.add_apply, Finsupp.sub_apply,
              Finsupp.single_eq_of_ne' hP, Finsupp.single_eq_of_ne' hQ, Finsupp.single_eq_same] <;>
              norm_num
          rw [show (WeierstrassCurve.Affine.Point.zero : Point n) = 0 by rfl, hk]
          exact vertical_origin_order n x₁
        | some u v hR =>
          have hx : x₂ = x₁ := hV.1.symm
          have hy : y₂ = -y₁ := by
            have he : y₁ = -y₂ := by simpa only [curve_negY] using hV.2
            simpa only [neg_neg] using (congrArg Neg.neg he).symm
          have hz := Finsupp.single_eq_of_ne (b := (1 : ℤ))
            (WeierstrassCurve.Affine.Point.some_ne_zero hR)
          have hk : geometricDivisor n P Q (.some u v hR) =
              ((pointMultiplicity u v x₁ (-y₁) + pointMultiplicity u v x₁ y₁ : ℕ) : ℤ) := by
            rw [geometricDivisor, hsum]
            simp only [Finsupp.add_apply, Finsupp.sub_apply, hz, P, Q, single_affine,
              hx, hy, sub_zero, Nat.cast_add, add_comm]
          rw [hk]
          exact actual_vertical_local_order n u v x₁ y₁ hn hR.left h₁
      · let W := (curve n).toAffine
        let a := W.slope x₁ x₂ y₁ y₂
        let z := W.addX x₁ x₂ a
        let w := W.addY x₁ x₂ y₁ a
        have hf : millerFunction n P Q = nonverticalFunction n x₁ y₁ a z := by
          simp only [P, Q, millerFunction, if_neg hV, a, z, W]
        have hsum : P + Q = .some z w (W.nonsingular_add h₁ h₂ hV) :=
          WeierstrassCurve.Affine.Point.add_some hV
        have hS : P + Q ≠ 0 := by
          rw [hsum]
          exact WeierstrassCurve.Affine.Point.some_ne_zero _
        rw [hf]
        cases R with
        | zero =>
          have hk : geometricDivisor n P Q 0 = -1 := by
            simp only [geometricDivisor, Finsupp.add_apply, Finsupp.sub_apply,
              Finsupp.single_eq_of_ne' hP, Finsupp.single_eq_of_ne' hQ,
              Finsupp.single_eq_of_ne' hS, Finsupp.single_eq_same] <;> norm_num
          rw [show (WeierstrassCurve.Affine.Point.zero : Point n) = 0 by rfl, hk]
          exact nonvertical_origin_order n x₁ y₁ a z
        | some u v hR =>
          have hz := Finsupp.single_eq_of_ne (b := (1 : ℤ))
            (WeierstrassCurve.Affine.Point.some_ne_zero hR)
          have hk : geometricDivisor n P Q (.some u v hR) =
              (((pointMultiplicity u v x₁ y₁ + pointMultiplicity u v x₂ y₂ : ℕ) : ℤ) -
                (pointMultiplicity u v z w : ℤ)) := by
            rw [geometricDivisor, hsum]
            simp only [Finsupp.add_apply, Finsupp.sub_apply, hz, P, Q, single_affine, sub_zero,
              Nat.cast_add]
          rw [hk]
          exact actual_nonvertical_local_order n u v x₁ y₁ x₂ y₂ hn hR.left h₁.left h₂.left hV

end ActualMillerGeometricDivisor318
