module
public import ActualGaussianWeberFiniteFibreSlope318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import all Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public section
noncomputable section

namespace ActualGaussianWeberFiniteFibreDifference318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberFiniteFibreSlope318

variable {F : Type*} [Field F] [DecidableEq F] (V : ValuationSubring F)


theorem literal_neg_y (x y : F) : WeierstrassCurve.Affine.negY ((curve F).toAffine) x y = -y := by simp [negY,curve,toAffine]

theorem literal_add_x (x y ell : F) : WeierstrassCurve.Affine.addX ((curve F).toAffine) x y ell = ell^2-x-y := by
  simp [addX,curve,toAffine]

/-- Actual stock P−Q reduces to O on the ordinary/ordinary same-fibre
branch. The nonvertical slope is allowed to be a tangent. -/
theorem finite_fibre_difference (h2 : (2:ResidueField V) ≠ 0) (hF : (2:F) ≠ 0)
    (a b c d : V)
    (hP : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) (V.subtype a) (V.subtype b))
    (hQ : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) (V.subtype c) (V.subtype d))
    (hx : residue V a=residue V c) (hy : residue V b=residue V d) :
    specialize V h2 (Point.some _ _ hP - Point.some _ _ hQ) = Point.zero := by
  rw [sub_eq_add_neg,Point.neg_some]
  by_cases hvert : V.subtype a=V.subtype c ∧
      V.subtype b=WeierstrassCurve.Affine.negY ((curve F).toAffine) (V.subtype c) (WeierstrassCurve.Affine.negY ((curve F).toAffine) (V.subtype c) (V.subtype d))
  · rw [Point.add_of_Y_eq hvert.1 hvert.2] <;> rfl
  rw [Point.add_some hvert]
  apply (specialize_some_eq_zero V h2 _).mpr
  rw [literal_add_x]
  apply subtraction_abscissa_pole V a.property c.property
  have he₁ := equation_in_subring V a b ((literal_equation _ _).mp hP.1)
  have he₂ := equation_in_subring V c d ((literal_equation _ _).mp hQ.1)
  by_cases hxF : V.subtype a=V.subtype c
  · have hyF : V.subtype b ≠ V.subtype d := by
      intro H
      apply hvert
      exact ⟨hxF,by rw [literal_neg_y,literal_neg_y,neg_neg,H]⟩
    have hsq : (V.subtype b)^2=(V.subtype d)^2 := by
      have h₁ := (literal_equation ..).mp hP.1
      have h₂ := (literal_equation ..).mp hQ.1
      rw [hxF] at h₁
      exact h₁.trans h₂.symm
    have hY : V.subtype b= -(V.subtype d) := by
      have hM : (V.subtype b-V.subtype d)*(V.subtype b+V.subtype d)=0 := by
        linear_combination hsq
      have hSum := (mul_eq_zero.mp hM).resolve_left (sub_ne_zero.mpr hyF)
      linear_combination hSum
    have hny : b = -d := V.subtype_injective (by rw [map_neg]; exact hY)
    have hb0 : residue V b=0 := by
      have ht : (residue V b)+(residue V b)=0 := by
        have he := congrArg (residue V) hny
        rw [map_neg,←hy] at he
        linear_combination he
      rw [←two_mul] at ht
      exact (mul_eq_zero.mp ht).resolve_left h2
    have hbF : V.subtype b ≠ 0 := by
      intro H
      apply hyF
      have Hd : V.subtype d=0 := by
        have h' : -(V.subtype d)=0 := hY.symm.trans H
        exact neg_eq_zero.mp h'
      exact H.trans Hd.symm
    have ht := mul_ne_zero hF hbF
    have hSl : WeierstrassCurve.Affine.slope ((curve F).toAffine) (V.subtype a) (V.subtype c) (V.subtype b) (WeierstrassCurve.Affine.negY ((curve F).toAffine) (V.subtype c) (V.subtype d)) =
        ((3:F)*(V.subtype a)^2-1)/((2:F)*V.subtype b) := by
      rw [slope_of_Y_ne hxF (fun H => hvert ⟨hxF,H⟩),literal_neg_y]
      simp only [curve,toAffine,mul_zero,zero_mul,add_zero,sub_zero]
      congr 1 <;> ring
    rw [hSl]
    exact residue_two_torsion_tangent_pole V h2 a b he₁ hb0 ht
  · rw [slope_of_X_ne hxF,literal_neg_y,sub_neg_eq_add]
    exact distinct_x_secant_pole V h2 a b c d he₁ he₂ hx hy hxF

end ActualGaussianWeberFiniteFibreDifference318
