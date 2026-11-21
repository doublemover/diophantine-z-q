module
public import ActualGaussianWeberOrdinarySlope318
public import ActualGaussianWeberFiniteFibreDifference318
public import ActualGaussianWeberReductionCoordinates318
public section
noncomputable section

namespace ActualGaussianWeberOrdinaryStock318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberReductionCoordinates318
open ActualGaussianWeberOrdinarySlope318

variable {F : Type*} [Field F] (V : ValuationSubring F)

private theorem some_transport {K : Type*} [CommRing K] {x y x' y' : K}
    {h : (curve K).toAffine.Nonsingular x y} {h' : (curve K).toAffine.Nonsingular x' y'}
    (hx : x=x') (hy : y=y') :
    Point.some x y h=Point.some x' y' h' := by
  subst x'
  subst y'
  rfl

theorem neg_integral_representative (a b : V)
    (h : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) (V.subtype a) (V.subtype b)) :
    ∃ hn : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) (V.subtype a) (V.subtype (-b)),
      -Point.some (V.subtype a) (V.subtype b) h =
       Point.some (V.subtype a) (V.subtype (-b)) hn := by
  have hy : WeierstrassCurve.Affine.negY ((curve F).toAffine) (V.subtype a) (V.subtype b)=V.subtype (-b) := by
    rw [ActualGaussianWeberOrdinarySlope318.literal_negY,map_neg]
  have hn : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) (V.subtype a) (V.subtype (-b)) := by
    rw [←hy]
    exact (nonsingular_neg ..).mpr h
  refine ⟨hn,?_⟩
  rw [Point.neg_some]
  exact some_transport rfl hy

/-- Negation holds with the same place and exact stock coordinates,
including the nonintegral x branch. -/
theorem specialize_neg (h2 : (2:ResidueField V) ≠ 0) (P : WP F) :
    specialize V h2 (-P)= -specialize V h2 P := by
  cases P with
  | zero => rfl
  | some x y hn =>
    by_cases hx : x∈V
    · let a : V := ⟨x,hx⟩
      let b : V := ⟨y,integral_y V ((literal_equation x y).mp hn.1) hx⟩
      obtain ⟨hNeg,hStock⟩ := neg_integral_representative V a b hn
      obtain ⟨hU,hRed⟩ := reduction_through_coordinates V h2 hn a b rfl rfl
      obtain ⟨hUN,hRedN⟩ := reduction_through_coordinates V h2 hNeg a (-b) rfl rfl
      rw [hStock,hRedN,hRed,Point.neg_some]
      exact some_transport rfl (by rw [map_neg,ActualGaussianWeberOrdinarySlope318.literal_negY])
    · have hP := (specialize_some_eq_zero V h2 hn).mpr hx
      have hK : specialize V h2 (-Point.some x y hn)=Point.zero := by
        rw [Point.neg_some]
        exact (specialize_some_eq_zero V h2 _).mpr hx
      rw [hK,hP] <;> rfl

variable [DecidableEq F] [DecidableEq (ResidueField V)]

private theorem add_of_nonopposite (h2 : (2:ResidueField V) ≠ 0) (a b c d : V)
    (hP : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) (V.subtype a) (V.subtype b))
    (hQ : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) (V.subtype c) (V.subtype d))
    (hN : ¬(residue V a=residue V c ∧ residue V b= -(residue V d))) :
    specialize V h2 (Point.some _ _ hP+Point.some _ _ hQ)=
       specialize V h2 (Point.some _ _ hP)+specialize V h2 (Point.some _ _ hQ) := by
  have he₁ := equation_in_subring V a b ((literal_equation _ _).mp hP.1)
  have he₂ := equation_in_subring V c d ((literal_equation _ _).mp hQ.1)
  obtain ⟨L⟩ := lift_of_nonopposite V a b c d he₁ he₂ hN
  let X : V := L.s^2-a-c
  let Y : V := -(L.s*(X-a)+b)
  let sF := WeierstrassCurve.Affine.slope ((curve F).toAffine) (V.subtype a) (V.subtype c) (V.subtype b) (V.subtype d)
  let sR := WeierstrassCurve.Affine.slope ((curve (ResidueField V)).toAffine) (residue V a) (residue V c) (residue V b) (residue V d)
  have hSF : sF=V.subtype L.s := L.generic.symm
  have hSR : sR=residue V L.s := L.residual.symm
  have hXF : WeierstrassCurve.Affine.addX ((curve F).toAffine) (V.subtype a) (V.subtype c) sF=V.subtype X := by
    rw [ActualGaussianWeberOrdinarySlope318.literal_addX,hSF]
    simp only [X,map_sub,map_pow]
  have hYF : WeierstrassCurve.Affine.addY ((curve F).toAffine) (V.subtype a) (V.subtype c) (V.subtype b) sF=V.subtype Y := by
    rw [ActualGaussianWeberOrdinarySlope318.literal_addY,hXF,hSF]
    simp only [Y,map_neg,map_add,map_mul,map_sub]
  have hXR : WeierstrassCurve.Affine.addX ((curve (ResidueField V)).toAffine) (residue V a) (residue V c) sR=residue V X := by
    rw [ActualGaussianWeberOrdinarySlope318.literal_addX,hSR]
    simp only [X,map_sub,map_pow]
  have hYR : WeierstrassCurve.Affine.addY ((curve (ResidueField V)).toAffine) (residue V a) (residue V c) (residue V b) sR=residue V Y := by
    rw [ActualGaussianWeberOrdinarySlope318.literal_addY,hXR,hSR]
    simp only [Y,map_neg,map_add,map_mul,map_sub]
  obtain ⟨rP,hRP⟩ := reduction_through_coordinates V h2 hP a b rfl rfl
  obtain ⟨rQ,hRQ⟩ := reduction_through_coordinates V h2 hQ c d rfl rfl
  obtain ⟨rS,hRS⟩ := reduction_through_coordinates V h2
    (nonsingular_add hP hQ L.generic_ne) X Y hXF hYF
  rw [Point.add_some L.generic_ne,hRS,hRP,hRQ,Point.add_some L.residue_ne]
  exact some_transport hXR.symm hYR.symm

/-- Exact ordinary×ordinary stock point reduction. The opposite
residue branch (including ȳ=0) reuses the independent actual
same-fibre difference for P−(−Q); the other branch lifts the genuine
stock slope, including a same-residue x secant or tangent. -/
theorem ordinary_add (hF : (2:F) ≠ 0) (h2 : (2:ResidueField V) ≠ 0)
    (a b c d : V) (hP : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) (V.subtype a) (V.subtype b))
    (hQ : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) (V.subtype c) (V.subtype d)) :
    specialize V h2 (Point.some _ _ hP+Point.some _ _ hQ)=
      specialize V h2 (Point.some _ _ hP)+specialize V h2 (Point.some _ _ hQ) := by
  by_cases hN : residue V a=residue V c ∧ residue V b= -(residue V d)
  · obtain ⟨hNeg,hStock⟩ := neg_integral_representative V c d hQ
    have hy : residue V b=residue V (-d) := by simpa only [map_neg] using hN.2
    have hDiff := ActualGaussianWeberFiniteFibreDifference318.finite_fibre_difference
      V h2 hF a b c (-d) hP hNeg hN.1 hy
    have hSum : Point.some _ _ hP-Point.some _ _ hNeg=Point.some _ _ hP+Point.some _ _ hQ := by
      rw [←hStock,sub_eq_add_neg,neg_neg]
    obtain ⟨rP,hRP⟩ := reduction_through_coordinates V h2 hP a b rfl rfl
    obtain ⟨rQ,hRQ⟩ := reduction_through_coordinates V h2 hQ c d rfl rfl
    rw [hSum] at hDiff
    rw [hDiff,hRP,hRQ,Point.add_of_Y_eq hN.1 (by simpa only [ActualGaussianWeberOrdinarySlope318.literal_negY] using hN.2)] <;> rfl
  · exact add_of_nonopposite V h2 a b c d hP hQ hN

end ActualGaussianWeberOrdinaryStock318
