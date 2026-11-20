module
public import ActualMillerAffineLocalChart318
public import ActualTwoDescentLocalizationFractionEquivalence318
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
import all ActualMillerNormalizedFunction318
import all ActualMillerRegularEvaluation318
import all ActualTwoDescentAffineChartCoordinates318
import all ActualTwoDescentOriginalFunctionFieldTheta318
public section
noncomputable section

namespace ActualMillerAffineValuation318

open ActualTwoDescentEllipticModel318 ActualTwoDescentAffineChartCoordinates318
open ActualTwoDescentOriginalFunctionFieldTheta318 ActualTwoDescentLocalizationFractionEquivalence318
open ActualMillerRegularEvaluation318 ActualMillerInfinityNormalization318
open ActualMillerAffineNormIdeal318 ActualMillerAffineLocalChart318
open WeierstrassCurve.Affine.CoordinateRing (XClass_ne_zero XYIdeal_neg_mul XIdeal)

variable {K : Type*} [Field K] [CharZero K]

def pointMultiplicity (u v x y : K) : ℕ := by
  classical
  exact if x = u ∧ y = v then 1 else 0

theorem map_point_ideal_power (n u v x y : K) (hR : (curve n).toAffine.Equation u v) :
    Ideal.map (affineLocalMap n u v hR) (pointIdeal n x y) =
      (IsLocalRing.maximalIdeal (AffineLocal n u v hR)) ^ pointMultiplicity u v x y := by
  classical
  by_cases h : x = u ∧ y = v
  · obtain ⟨rfl, rfl⟩ := h
    simpa only [pointMultiplicity, if_pos (And.intro rfl rfl), pow_one] using
      map_point_ideal_self n u v hR
  · rw [map_point_ideal_other n u v x y hR h]
    simp only [pointMultiplicity, if_neg h, pow_zero, Ideal.one_eq_top]

abbrev LocalField (n u v : K) (hR : (curve n).toAffine.Equation u v) :=
  FractionRing (AffineLocal n u v hR)

abbrev toLocalField (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    AffineLocal n u v hR →+* LocalField n u v hR := algebraMap _ _

def localFieldEquiv (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    OriginalFunctionField n ≃+* LocalField n u v hR :=
  localizationFractionEquiv (AffineChart n) (AffineLocal n u v hR)
    (pointKernel n u v hR).primeCompl (affineLocal_injective n u v hR)

theorem local_field_on_base (n u v : K) (hR : (curve n).toAffine.Equation u v)
    (c : AffineChart n) :
    localFieldEquiv n u v hR (fractionalBase n c) =
      toLocalField n u v hR (affineLocalMap n u v hR c) :=
  actual_localization_fraction_equiv_base (AffineChart n) (AffineLocal n u v hR)
    (pointKernel n u v hR).primeCompl (affineLocal_injective n u v hR) c

private theorem same_function_fraction (n x y a z : K) :
    nonverticalFunction n x y a z =
      fractionalBase n (lineNumerator n x y a) / fractionalBase n (vertical n z) := by
  simp only [nonverticalFunction, lineNumerator_coordinates, vertical_coordinates,
    map_mul, map_add, map_sub] <;> rfl

/-- No factorization of principal ideals is used. An equality of two
singleton spans is exactly association, which supplies the actual unit. -/
theorem unit_power_of_cleared_ideal {A F : Type*} [CommRing A] [IsDomain A] [Field F]
    (g : A →+* F) (hg : Function.Injective g) (N D π : A) (hD : D ≠ 0) (hπ : π ≠ 0)
    (i j : ℕ)
    (h : Ideal.span {D} * (Ideal.span {π})^i = Ideal.span {N} * (Ideal.span {π})^j) :
    ∃ e : Aˣ, g N / g D = g (e : A) * (g π)^((i : ℤ) - (j : ℤ)) := by
  have h' := h
  simp only [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton] at h'
  obtain ⟨e, he⟩ := Ideal.span_singleton_eq_span_singleton.mp h'
  have he' : (g D * (g π)^i) * g (e : A) = g N * (g π)^j := by
    simpa only [map_mul, map_pow] using congrArg g he
  have hD' : g D ≠ 0 := fun hd => hD (hg (by simpa only [map_zero] using hd))
  have hπ' : g π ≠ 0 := fun hp => hπ (hg (by simpa only [map_zero] using hp))
  refine ⟨e, ?_⟩
  rw [zpow_sub₀ hπ', zpow_natCast, zpow_natCast]
  calc
    _ = (g N * (g π)^j) / (g D * (g π)^j) := by field_simp [hD', hπ'] <;> ring
    _ = _ := by rw [← he']; field_simp [hD', hπ'] <;> ring

variable [DecidableEq K]

theorem localized_line_ideal_balance (n u v x₁ y₁ x₂ y₂ : K)
    (hR : (curve n).toAffine.Equation u v)
    (h₁ : (curve n).toAffine.Equation x₁ y₁)
    (h₂ : (curve n).toAffine.Equation x₂ y₂)
    (hInv : ¬(x₁ = x₂ ∧ y₁ = (curve n).toAffine.negY x₂ y₂)) :
    let W := (curve n).toAffine
    let a := W.slope x₁ x₂ y₁ y₂
    let z := W.addX x₁ x₂ a
    let w := W.addY x₁ x₂ y₁ a
    let f := affineLocalMap n u v hR
    let J := IsLocalRing.maximalIdeal (AffineLocal n u v hR)
    Ideal.span {f (vertical n z)} * J^(pointMultiplicity u v x₁ y₁ + pointMultiplicity u v x₂ y₂) =
      Ideal.span {f (lineNumerator n x₁ y₁ a)} * J^(pointMultiplicity u v z w) := by
  dsimp only
  have h := congrArg (Ideal.map (affineLocalMap n u v hR))
    (affine_line_ideal_identity n x₁ y₁ x₂ y₂ h₁ h₂ hInv)
  simpa only [Ideal.map_mul, map_point_ideal_power, Ideal.map_span, Set.image_singleton,
    ← pow_add] using h

/-- Exact affine local order of the SAME meromorphic line ratio. This
applies at collision points, without requiring the point-value
denominator to be invertible. All coincidences of the three
summands are retained in the integer exponent. -/
theorem actual_nonvertical_local_order (n u v x₁ y₁ x₂ y₂ : K) (hn : n ≠ 0)
    (hR : (curve n).toAffine.Equation u v)
    (h₁ : (curve n).toAffine.Equation x₁ y₁)
    (h₂ : (curve n).toAffine.Equation x₂ y₂)
    (hInv : ¬(x₁ = x₂ ∧ y₁ = (curve n).toAffine.negY x₂ y₂)) :
    let W := (curve n).toAffine
    let a := W.slope x₁ x₂ y₁ y₂
    let z := W.addX x₁ x₂ a
    let w := W.addY x₁ x₂ y₁ a
    ∃ π : AffineLocal n u v hR, Irreducible π ∧ ∃ e : (AffineLocal n u v hR)ˣ,
      localFieldEquiv n u v hR (nonverticalFunction n x₁ y₁ a z) =
        toLocalField n u v hR (e : AffineLocal n u v hR) *
        (toLocalField n u v hR π)^
          (((pointMultiplicity u v x₁ y₁ + pointMultiplicity u v x₂ y₂ : ℕ) : ℤ) -
            (pointMultiplicity u v z w : ℤ)) := by
  dsimp only
  let W := (curve n).toAffine
  let a := W.slope x₁ x₂ y₁ y₂
  let z := W.addX x₁ x₂ a
  let w := W.addY x₁ x₂ y₁ a
  let f := affineLocalMap n u v hR
  letI := actual_affine_local_DVR n u v hn hR
  obtain ⟨π, hπ, hJ⟩ := actual_affine_local_principal n u v hn hR
  refine ⟨π, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπ hJ, ?_⟩
  have h := localized_line_ideal_balance n u v x₁ y₁ x₂ y₂ hR h₁ h₂ hInv
  dsimp only at h
  rw [hJ] at h
  have hD : f (vertical n z) ≠ 0 := by
    intro he
    exact XClass_ne_zero z (affineLocal_injective n u v hR (by simpa only [map_zero] using he))
  obtain ⟨e, he⟩ := unit_power_of_cleared_ideal (toLocalField n u v hR)
    (IsFractionRing.injective (AffineLocal n u v hR) (LocalField n u v hR))
    (f (lineNumerator n x₁ y₁ a)) (f (vertical n z)) π hD hπ
    (pointMultiplicity u v x₁ y₁ + pointMultiplicity u v x₂ y₂) (pointMultiplicity u v z w) h
  refine ⟨e, ?_⟩
  simp only [same_function_fraction, map_div₀, local_field_on_base]
  exact he

/-- The vertical branch counts both P and −P; at a ramification
point they are equal and the affine order is two. -/
theorem actual_vertical_local_order (n u v x y : K) (hn : n ≠ 0)
    (hR : (curve n).toAffine.Equation u v) (hP : (curve n).toAffine.Nonsingular x y) :
    ∃ π : AffineLocal n u v hR, Irreducible π ∧ ∃ e : (AffineLocal n u v hR)ˣ,
      localFieldEquiv n u v hR (rootFunction n x) =
        toLocalField n u v hR (e : AffineLocal n u v hR) *
        (toLocalField n u v hR π)^
          ((pointMultiplicity u v x (-y) + pointMultiplicity u v x y : ℕ) : ℤ) := by
  let f := affineLocalMap n u v hR
  letI := actual_affine_local_DVR n u v hn hR
  obtain ⟨π, hπ, hJ⟩ := actual_affine_local_principal n u v hn hR
  refine ⟨π, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπ hJ, ?_⟩
  have h := congrArg (Ideal.map f) (XYIdeal_neg_mul hP)
  have h' : (Ideal.span {π})^(pointMultiplicity u v x (-y) + pointMultiplicity u v x y) =
      Ideal.span {f (vertical n x)} := by
    change Ideal.map (affineLocalMap n u v hR)
      (pointIdeal n x ((curve n).toAffine.negY x y) * pointIdeal n x y) =
        Ideal.map (affineLocalMap n u v hR) (Ideal.span {vertical n x}) at h
    simpa only [curve_negY, Ideal.map_mul, map_point_ideal_power, hJ, ← pow_add,
      Ideal.map_span, Set.image_singleton] using h
  have hbalance : Ideal.span {(1 : AffineLocal n u v hR)} *
      (Ideal.span {π})^(pointMultiplicity u v x (-y) + pointMultiplicity u v x y) =
      Ideal.span {f (vertical n x)} * (Ideal.span {π})^0 := by
    simpa only [Ideal.span_singleton_one, ← Ideal.one_eq_top, one_mul, pow_zero, mul_one] using h'
  obtain ⟨e, he⟩ := unit_power_of_cleared_ideal (toLocalField n u v hR)
    (IsFractionRing.injective (AffineLocal n u v hR) (LocalField n u v hR))
    (f (vertical n x)) 1 π one_ne_zero hπ _ 0 hbalance
  refine ⟨e, ?_⟩
  change localFieldEquiv n u v hR (fractionalBase n (vertical n x)) = _
  rw [local_field_on_base]
  simpa only [map_one, div_one, Nat.cast_zero, sub_zero] using he

end ActualMillerAffineValuation318
