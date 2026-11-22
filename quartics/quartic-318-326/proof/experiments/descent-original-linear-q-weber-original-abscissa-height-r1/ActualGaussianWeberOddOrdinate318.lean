module
public import ActualGaussianWeberOddNormGeneric318
public section
noncomputable section

namespace ActualGaussianWeberOddOrdinate318

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberQuadraticGenericChart318
open ActualGaussianWeberGenericChartDomain318 ActualGaussianWeberGaussLocalization318
open ActualGaussianWeberTranslationChart318 ActualGaussianWeberTranslationFunctionField318
open ActualGaussianWeberOddNormGeneric318 ActualGaussianWeberStockCoordinateHom318
open ActualGaussianWeberPlaceEquivariance318 ActualGaussianWeberOrdinarySlope318
open ActualGaussianWeberGaussianScalarSpecialization318

variable (k : Type*) [Field k]

@[expose] def ofX : k[X]→+*Chart k := AdjoinRoot.of (relation k)

theorem ofX_injective : Function.Injective (ofX k) := by
  intro a b h
  have h' : (element a (0:k[X]) : Chart k)=element b 0 := by
    simpa only [element,map_zero,zero_mul,add_zero] using h
  exact (element_coefficients h').1

private theorem reflected_root : (relation k).eval₂ (ofX k) (-yChart k)=0 := by
  change (((X : (k[X])[X])^2 - C ((X : k[X])^3-X))).eval₂ (ofX k) (-yChart k)=0
  rw [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,map_sub,map_pow,neg_sq]
  change (yChart k)^2-((xChart k)^3-xChart k)=0
  exact sub_eq_zero.mpr (equation_chart k)

@[expose] def reflectChart : Chart k→+*Chart k :=
  AdjoinRoot.lift (ofX k) (-yChart k) (reflected_root k)

theorem reflect_polynomial (P : k[X]) : reflectChart k (ofX k P)=ofX k P :=
  AdjoinRoot.lift_of (reflected_root k)

theorem reflect_y : reflectChart k (yChart k)= -yChart k :=
  AdjoinRoot.lift_root (reflected_root k)

theorem reflect_element (A B : k[X]) :
    reflectChart k (element A B)=element A (-B) := by
  change reflectChart k (ofX k A+ofX k B*yChart k)=ofX k A+ofX k (-B)*yChart k
  rw [map_add,map_mul,reflect_polynomial,reflect_polynomial,reflect_y,map_neg,mul_neg,neg_mul]

theorem reflect_twice (z : Chart k) : reflectChart k (reflectChart k z)=z := by
  obtain ⟨A,B,h⟩ := element_surjective z
  rw [←h,reflect_element,reflect_element,neg_neg]

theorem reflect_injective : Function.Injective (reflectChart k) :=
  Function.LeftInverse.injective (reflect_twice k)

@[expose] def reflectFrac : FunctionField k→+*FunctionField k :=
  IsFractionRing.lift ((fractionMap_injective k).comp (reflect_injective k))

theorem reflect_frac_chart (z : Chart k) :
    reflectFrac k (fractionMap k z)=fractionMap k (reflectChart k z) :=
  IsFractionRing.lift_algebraMap ((fractionMap_injective k).comp (reflect_injective k)) z

theorem reflect_frac_x : reflectFrac k (xGeneric k)=xGeneric k := by
  change reflectFrac k (fractionMap k (ofX k X))=_
  rw [reflect_frac_chart,reflect_polynomial] <;> rfl

theorem reflect_frac_y : reflectFrac k (yGeneric k)= -yGeneric k := by
  change reflectFrac k (fractionMap k (yChart k))=_
  rw [reflect_frac_chart,reflect_y,map_neg] <;> rfl

theorem reflect_frac_const (c : k) : reflectFrac k (constGeneric k c)=constGeneric k c := by
  change reflectFrac k (fractionMap k (ofX k (C c)))=_
  rw [reflect_frac_chart,reflect_polynomial] <;> rfl

private theorem free_two {A : k[X]} (h2 : (2:k)≠0) (h : -A=A) : A=0 := by
  have hC : C (2:k)*A=0 := by
    calc
      _ = A+A := by rw [map_ofNat]; ring
      _ = A+ -A := congrArg (A+·) h.symm
      _ = _ := add_neg_cancel _
  exact (mul_eq_zero.mp hC).resolve_left
    (fun h => h2 (C_injective (h.trans C_0.symm)))

/-- Literal anti-invariant part of the function field. Multiply by
the conjugate of the original chart denominator, which is nonzero.
The new denominator is even and the numerator odd on the exact free
basis (1,Y). No unproved separability or geometric continuation is used. -/
theorem odd_fraction (h2 : (2:k)≠0) (v : FunctionField k)
    (h : reflectFrac k v= -v) :
    ∃ U D : k[X], D≠0 ∧ v=(fractionMap k (ofX k U)/fractionMap k (ofX k D))*yGeneric k := by
  letI : IsDomain (Chart k) := chart_isDomain k
  obtain ⟨N,D,hD₀,hv⟩ := IsFractionRing.div_surjective (Chart k) v
  have hD : D≠0 := mem_nonZeroDivisors_iff_ne_zero.mp hD₀
  have hv' : v=fractionMap k N/fractionMap k D := hv.symm
  let E := D*reflectChart k D
  let Z := N*reflectChart k D
  have hDr : reflectChart k D≠0 :=
    fun H => hD (reflect_injective k (H.trans (map_zero _).symm))
  have hE : E≠0 := mul_ne_zero hD hDr
  have he0 : fractionMap k E≠0 :=
    fun H => hE (fractionMap_injective k (H.trans (map_zero _).symm))
  have hRE : reflectChart k E=E := by
    change reflectChart k (D*reflectChart k D)=D*reflectChart k D
    rw [map_mul,reflect_twice,mul_comm]
  have hEq : v=fractionMap k Z/fractionMap k E := by
    have hn : fractionMap k D≠0 :=
      fun H => hD (fractionMap_injective k (H.trans (map_zero _).symm))
    apply (eq_div_iff he0).mpr
    change v*fractionMap k (D*reflectChart k D)=fractionMap k (N*reflectChart k D)
    rw [map_mul,map_mul,←mul_assoc,(eq_div_iff hn).mp hv']
  have hRZ : reflectChart k Z= -Z := by
    apply fractionMap_injective k
    have hh : reflectFrac k v=fractionMap k (reflectChart k Z)/fractionMap k E := by
      rw [hEq,map_div₀,reflect_frac_chart,reflect_frac_chart,hRE]
    rw [h,hEq,neg_div] at hh
    rw [map_neg]
    exact mul_right_cancel₀ he0 (by
      have q := congrArg (fun u : FunctionField k => u*fractionMap k E) hh.symm
      simpa only [div_mul_cancel₀ _ he0] using q)
  obtain ⟨U,V,hN⟩ := element_surjective Z
  obtain ⟨C,D₁,hDe⟩ := element_surjective E
  have eD : -D₁=D₁ := by
    rw [←hDe,reflect_element] at hRE
    exact (element_coefficients hRE).2
  have eN : -U=U := by
    rw [←hN,reflect_element] at hRZ
    have eqNeg : -(element U V:Chart k)=element (-U) (-V) := by
      change -(ofX k U+ofX k V*yChart k)=ofX k (-U)+ofX k (-V)*yChart k
      rw [neg_add_rev,map_neg,map_neg,neg_mul,add_comm]
    rw [eqNeg] at hRZ
    exact (element_coefficients hRZ).1.symm
  have hD₁ : D₁=0 := free_two k h2 eD
  have hU : U=0 := free_two k h2 eN
  have hDe' : E=ofX k C := by
    rw [←hDe,hD₁]
    change ofX k C+ofX k 0*yChart k=_
    rw [map_zero,zero_mul,add_zero]
  have hC : C≠0 := fun hh => hE (by rw [hDe',hh,map_zero])
  refine ⟨V,C,hC,?_⟩
  rw [hEq,←hN,hU,hDe']
  change fractionMap k (ofX k 0+ofX k V*yChart k)/fractionMap k (ofX k C)=_
  rw [map_zero,zero_add,map_mul]
  change (fractionMap k (ofX k V)*yGeneric k)/fractionMap k (ofX k C)=_
  ring

@[expose] def polyFrac : k[X]→+*FunctionField k := (fractionMap k).comp (ofX k)

theorem polyFrac_injective : Function.Injective (polyFrac k) :=
  (fractionMap_injective k).comp (ofX_injective k)

@[expose] def ratFrac : RatFunc k→+*FunctionField k :=
  IsFractionRing.lift (polyFrac_injective k)

theorem ratFrac_poly (P : k[X]) : ratFrac k (algebraMap k[X] (RatFunc k) P)=polyFrac k P :=
  IsFractionRing.lift_algebraMap (polyFrac_injective k) P

theorem ratFrac_mk (A B : k[X]) : ratFrac k (RatFunc.mk A B)=polyFrac k A/polyFrac k B := by
  rw [RatFunc.mk_eq_div,map_div₀,ratFrac_poly,ratFrac_poly]

theorem ratFrac_normalized (r : RatFunc k) :
    polyFrac k r.num/polyFrac k r.denom=ratFrac k r := by
  rw [←ratFrac_poly,←ratFrac_poly,←map_div₀,RatFunc.num_div_denom]

private theorem ordinate_eq {F : Type*} [Field F] {x y z w : F}
    {h : (curve F).toAffine.Nonsingular x y} {j : (curve F).toAffine.Nonsingular z w}
    (e : Point.some x y h=Point.some z w j) : y=w :=
  congrArg (fun P : WP F => match P with | .zero => 0 | .some _ v _ => v) e

variable [DecidableEq (FunctionField k)]

theorem reflect_generic_point (h2 : (2:k)≠0) :
    coordinateHom (reflectFrac k) (function_two_ne k h2) (genericPoint k h2)=
      -(genericPoint k h2) := by
  change onCurvePoint (reflectFrac k) (function_two_ne k h2)
      (Point.some (xGeneric k) (yGeneric k)
        (nonsing_of_equation (function_two_ne k h2) (equation_generic k))) =
    -(Point.some (xGeneric k) (yGeneric k)
      (nonsing_of_equation (function_two_ne k h2) (equation_generic k)))
  rw [point_some,Point.neg_some]
  exact some_congr (reflect_frac_x k) ((reflect_frac_y k).trans (literal_negY _ _ _).symm)

/-- For the literal finite generic scalar it is the actual **ordinate**
that is odd, because the exact coefficient-fixing involution is negation
on the source point and the Gaussian endomorphism respects negation. -/
theorem scalar_ordinate_odd (h2 : (2:k)≠0) (i : k) (hi : i^2= -1)
    (a b : ℤ) (u v : FunctionField k)
    (huv : (curve (FunctionField k)).toAffine.Nonsingular u v)
    (hG : gaussian (function_two_ne k h2) (constGeneric k i)
      (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi)
      a b (genericPoint k h2)=Point.some u v huv) :
    reflectFrac k v= -v := by
  let hF := function_two_ne k h2
  let j := constGeneric k i
  have hj : j^2= -1 := by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi
  have h := coordinate_gaussian (reflectFrac k) hF hF j j hj hj (reflect_frac_const k i) a b
    (genericPoint k h2)
  rw [reflect_generic_point k h2,map_neg,hG] at h
  change onCurvePoint (reflectFrac k) hF (Point.some u v huv)=-(Point.some u v huv) at h
  rw [point_some,Point.neg_some] at h
  exact (ordinate_eq h).trans (literal_negY _ _ _)

/-- The exact cleared original curve equation. Its U,V come from the
actual affine ordinate, not a second independent pair supplied by a caller. -/
theorem cleared_ordinate (h2 : (2:k)≠0)
    (A B : k[X]) (hB : B≠0) (u v : FunctionField k)
    (huv : (curve (FunctionField k)).toAffine.Nonsingular u v)
    (hx : u=polyFrac k A/polyFrac k B) (hy : reflectFrac k v= -v) :
    ∃ U V : k[X], IsCoprime U V ∧ V≠0 ∧
      U^2*((Polynomial.X:k[X])^3-Polynomial.X)*B^3=V^2*(A^3-A*B^2) := by
  obtain ⟨U₀,V₀,_,h₀⟩ := odd_fraction k h2 v hy
  let r := RatFunc.mk U₀ V₀
  let U := r.num
  let V := r.denom
  have hV : V≠0 := RatFunc.denom_ne_zero r
  have hY : v=(polyFrac k U/polyFrac k V)*yGeneric k := by
    rw [ratFrac_normalized k r,ratFrac_mk]
    exact h₀
  have hD : polyFrac k B≠0 :=
    fun h => hB (polyFrac_injective k (h.trans (map_zero _).symm))
  have hE : polyFrac k V≠0 :=
    fun h => hV (polyFrac_injective k (h.trans (map_zero _).symm))
  have he := (literal_equation u v).mp huv.1
  rw [hY,hx,mul_pow,equation_generic] at he
  refine ⟨U,V,RatFunc.isCoprime_num_denom r,hV,?_⟩
  apply polyFrac_injective k
  simp only [map_mul,map_sub,map_pow]
  change (polyFrac k U)^2*((xGeneric k)^3-xGeneric k)*(polyFrac k B)^3=
    (polyFrac k V)^2*((polyFrac k A)^3-polyFrac k A*(polyFrac k B)^2)
  have hu₂ : (polyFrac k U/polyFrac k V)^2*(polyFrac k V)^2=(polyFrac k U)^2 := by
    rw [div_pow,div_mul_cancel₀ _ (pow_ne_zero 2 hE)]
  have ha₃ : (polyFrac k A/polyFrac k B)^3*(polyFrac k B)^3=(polyFrac k A)^3 := by
    rw [div_pow,div_mul_cancel₀ _ (pow_ne_zero 3 hD)]
  have ha₁ : (polyFrac k A/polyFrac k B)*(polyFrac k B)^3=polyFrac k A*(polyFrac k B)^2 := by
    calc
      _ = ((polyFrac k A/polyFrac k B)*polyFrac k B)*(polyFrac k B)^2 := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hD]
  calc
    _ = (((polyFrac k U/polyFrac k V)^2)*((xGeneric k)^3-xGeneric k))*
        ((polyFrac k V)^2*(polyFrac k B)^3) := by rw [←hu₂] <;> ring
    _ = _ := by rw [he]
    _ = _ := by rw [←ha₃,←ha₁] <;> ring

end ActualGaussianWeberOddOrdinate318
