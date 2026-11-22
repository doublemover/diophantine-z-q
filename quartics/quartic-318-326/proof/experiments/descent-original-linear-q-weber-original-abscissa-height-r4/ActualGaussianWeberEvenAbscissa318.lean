module
public import ActualGaussianWeberOddOrdinate318
public section
noncomputable section

namespace ActualGaussianWeberEvenAbscissa318

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberOrdinarySlope318
open ActualGaussianWeberGaussianScalarSpecialization318 ActualGaussianWeberOddNormGeneric318
open ActualGaussianWeberQuadraticGenericChart318 ActualGaussianWeberGaussLocalization318
open ActualGaussianWeberTranslationFunctionField318 ActualGaussianWeberGenericChartDomain318
open ActualGaussianWeberOddOrdinate318

variable (k : Type*) [Field k]

theorem fixed_chart_polynomial (h2 : (2:k)≠0) (U : Chart k) (h : reflectChart k U=U) :
    ∃ a : k[X], U=ofX k a := by
  obtain ⟨a,b,hU⟩ := element_surjective U
  rw [←hU,reflect_element] at h
  have hb := (element_coefficients h).2
  have e : C (2:k)*b=0 := by
    calc
      _ = b+b := by rw [map_ofNat]; ring
      _ = b+ -b := congrArg (b+·) hb.symm
      _ = _ := add_neg_cancel _
  have hb0 : b=0 := (mul_eq_zero.mp e).resolve_left
    (fun z => h2 (C_injective (z.trans C_0.symm)))
  refine ⟨a,?_⟩
  rw [←hU,hb0]
  change ofX k a+ofX k 0*AdjoinRoot.root (relation k)=_
  rw [map_zero,zero_mul,add_zero]

/-- The even part of the actual fraction field is precisely its
embedded rational x-functions. The denominator is not assumed to
be even: multiply by its genuine conjugate before classification. -/
theorem fixed_fraction_is_rational (h2 : (2:k)≠0) (u : FunctionField k)
    (h : reflectFrac k u=u) :
    ∃ r : RatFunc k, u=ratFrac k r := by
  letI : IsDomain (Chart k) := chart_isDomain k
  obtain ⟨N,D,hD₀,hu⟩ := IsFractionRing.div_surjective (Chart k) u
  have hD : D≠0 := mem_nonZeroDivisors_iff_ne_zero.mp hD₀
  have hu' : u=fractionMap k N/fractionMap k D := hu.symm
  let E := D*reflectChart k D
  let Z := N*reflectChart k D
  have hDr : reflectChart k D≠0 := fun H => hD (reflect_injective k (H.trans (map_zero _).symm))
  have hE : E≠0 := mul_ne_zero hD hDr
  have he0 : fractionMap k E≠0 :=
    fun H => hE (fractionMap_injective k (H.trans (map_zero _).symm))
  have hRE : reflectChart k E=E := by
    change reflectChart k (D*reflectChart k D)=D*reflectChart k D
    rw [map_mul,reflect_twice,mul_comm]
  have hEq : u=fractionMap k Z/fractionMap k E := by
    have hn : fractionMap k D≠0 := fun H => hD (fractionMap_injective k (H.trans (map_zero _).symm))
    apply (eq_div_iff he0).mpr
    change u*fractionMap k (D*reflectChart k D)=fractionMap k (N*reflectChart k D)
    rw [map_mul,map_mul,←mul_assoc,(eq_div_iff hn).mp hu']
  have hRZ : reflectChart k Z=Z := by
    apply fractionMap_injective k
    have e : reflectFrac k u=fractionMap k (reflectChart k Z)/fractionMap k E := by
      rw [hEq,map_div₀,reflect_frac_chart,reflect_frac_chart,hRE]
    rw [h,hEq] at e
    have q := congrArg (fun r : FunctionField k => r*fractionMap k E) e
    simpa only [div_mul_cancel₀ _ he0] using q.symm
  obtain ⟨A,hA⟩ := fixed_chart_polynomial k h2 Z hRZ
  obtain ⟨B,hB⟩ := fixed_chart_polynomial k h2 E hRE
  refine ⟨RatFunc.mk A B,?_⟩
  rw [hEq,hA,hB,ratFrac_mk] <;> rfl

private theorem xcoord_eq {F : Type*} [Field F] {x y z w : F}
    {h : (curve F).toAffine.Nonsingular x y} {j : (curve F).toAffine.Nonsingular z w}
    (e : Point.some x y h=Point.some z w j) : x=z :=
  congrArg (fun P : WP F => match P with | .zero => 0 | .some x _ _ => x) e

variable [DecidableEq (FunctionField k)]

/-- The actual finite generic scalar's abscissa is the canonical
RatFunc ratio, with its own coprime numerator and denominator.
No degree statement is imported or hidden in the constructor. -/
theorem scalar_actual_x_ratio (h2 : (2:k)≠0) (i : k) (hi : i^2= -1)
    (a b : ℤ) (u v : FunctionField k)
    (huv : (curve (FunctionField k)).toAffine.Nonsingular u v)
    (hG : gaussian (function_two_ne k h2) (constGeneric k i)
      (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi)
      a b (genericPoint k h2)=Point.some u v huv) :
    ∃ r : RatFunc k, IsCoprime r.num r.denom ∧ r.denom≠0 ∧
      u=polyFrac k r.num/polyFrac k r.denom := by
  let hF := function_two_ne k h2
  let j := constGeneric k i
  have hj : j^2= -1 := by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi
  have h := coordinate_gaussian (reflectFrac k) hF hF j j hj hj (reflect_frac_const k i) a b
    (genericPoint k h2)
  rw [reflect_generic_point k h2,map_neg,hG] at h
  change onCurvePoint (reflectFrac k) hF (Point.some u v huv)=-(Point.some u v huv) at h
  rw [point_some,Point.neg_some] at h
  obtain ⟨r,hr⟩ := fixed_fraction_is_rational k h2 u (xcoord_eq h)
  exact ⟨r,RatFunc.isCoprime_num_denom r,RatFunc.denom_ne_zero r,hr.trans (ratFrac_normalized k r).symm⟩

end ActualGaussianWeberEvenAbscissa318
