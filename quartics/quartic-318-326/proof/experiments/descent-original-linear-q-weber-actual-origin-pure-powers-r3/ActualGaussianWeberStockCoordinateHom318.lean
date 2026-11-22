module
public import ActualGaussianWeberPlaceEquivariance318
public import ActualGaussianWeberOrdinarySlope318
public section
noncomputable section

namespace ActualGaussianWeberStockCoordinateHom318

open WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberOrdinarySlope318

variable {K L : Type*} [Field K] [Field L] [DecidableEq K] [DecidableEq L]

theorem point_some (f : K→+*L) (hL : (2:L)≠0)
    {x y : K} (h : (curve K).toAffine.Nonsingular x y) :
    onCurvePoint f hL (Point.some x y h)=Point.some (f x) (f y) (mapped_nonsingular f hL h) :=
  rfl

theorem some_congr {x y x' y' : L}
    {h : (curve L).toAffine.Nonsingular x y} {h' : (curve L).toAffine.Nonsingular x' y'}
    (hx : x=x') (hy : y=y') : Point.some x y h=Point.some x' y' h' := by
  subst x'
  subst y'
  rfl

private theorem opposite_iff (f : K→+*L) (x z y w : K) :
    (f x=f z ∧ f y=(curve L).toAffine.negY (f z) (f w)) ↔
      (x=z ∧ y=(curve K).toAffine.negY z w) := by
  simp only [literal_negY,←map_neg,f.injective.eq_iff]

private theorem slope_naturality (f : K→+*L) {x z y w : K}
    (h : ¬(x=z ∧ y=(curve K).toAffine.negY z w)) :
    f ((curve K).toAffine.slope x z y w)=(curve L).toAffine.slope (f x) (f z) (f y) (f w) := by
  by_cases hx : x=z
  · have hy : y≠ -w := fun hn => h ⟨hx,by simpa only [literal_negY] using hn⟩
    have hy' : f y≠ -(f w) := by
      intro hn
      exact hy (f.injective (by simpa only [map_neg] using hn))
    rw [literal_tangent_slope hx hy,literal_tangent_slope (congrArg f hx) hy']
    simp only [map_div₀,map_sub,map_mul,map_pow,map_ofNat,map_one]
  · have hl : f x≠ f z := fun h => hx (f.injective h)
    rw [slope_of_X_ne hx,slope_of_X_ne hl]
    simp only [map_div₀,map_sub]

private theorem addX_naturality (f : K→+*L) (x z s : K) :
    f ((curve K).toAffine.addX x z s)=(curve L).toAffine.addX (f x) (f z) (f s) := by
  simp only [literal_addX,map_sub,map_pow]

private theorem addY_naturality (f : K→+*L) (x z y s : K) :
    f ((curve K).toAffine.addY x z y s)=(curve L).toAffine.addY (f x) (f z) (f y) (f s) := by
  simp only [literal_addY,map_neg,map_add,map_mul,map_sub,addX_naturality]

/-- The actual coordinate map on the same literal model is an
additive homomorphism. This compares the stock point formulas, not a
separately chosen group action. -/
theorem coordinate_add (f : K→+*L) (hL : (2:L)≠0) (P Q : WP K) :
    onCurvePoint f hL (P+Q)=onCurvePoint f hL P+onCurvePoint f hL Q := by
  cases P with
  | zero =>
    change onCurvePoint f hL (0+Q)=0+onCurvePoint f hL Q
    simp only [zero_add]
  | some x y hP =>
    cases Q with
    | zero =>
      change onCurvePoint f hL (Point.some x y hP+0)=onCurvePoint f hL (Point.some x y hP)+0
      simp only [add_zero]
    | some z w hQ =>
      by_cases h : x=z ∧ y=(curve K).toAffine.negY z w
      · have hl := (opposite_iff f x z y w).mpr h
        rw [Point.add_of_Y_eq h.1 h.2,point_some f hL hP,point_some f hL hQ,
          Point.add_of_Y_eq hl.1 hl.2] <;> rfl
      · have hl := fun H => h ((opposite_iff f x z y w).mp H)
        rw [Point.add_some h,point_some f hL hP,point_some f hL hQ,Point.add_some hl,
          point_some f hL (nonsingular_add hP hQ h)]
        have hs := slope_naturality f h
        exact some_congr (by rw [addX_naturality,hs]) (by rw [addY_naturality,hs])

@[expose] def coordinateHom (f : K→+*L) (hL : (2:L)≠0) : WP K→+WP L where
  toFun := onCurvePoint f hL
  map_zero' := rfl
  map_add' := coordinate_add f hL

end ActualGaussianWeberStockCoordinateHom318
