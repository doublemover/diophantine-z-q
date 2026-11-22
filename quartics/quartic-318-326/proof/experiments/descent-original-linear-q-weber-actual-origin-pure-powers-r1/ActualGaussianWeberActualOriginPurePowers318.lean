module
public import ActualGaussianWeberLiteralOriginPole318
public import ActualGaussianWeberRationalDerivativeCap318
public import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.CharP.Frobenius
public section
noncomputable section

namespace ActualGaussianWeberActualOriginPurePowers318

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberOrdinarySlope318
open ActualGaussianWeberQuadraticGenericChart318 ActualGaussianWeberGaussLocalization318
open ActualGaussianWeberTranslationFunctionField318 ActualGaussianWeberOddNormGeneric318
open ActualGaussianWeberGaussianScalarSpecialization318
open ActualGaussianWeberLiteralOriginPole318 ActualGaussianWeberRationalDerivativeCap318

private def xCoord {F : Type*} [CommRing F] : WP F → F
  | Point.zero => 0
  | Point.some x _ _ => x

private theorem translate_T₀_x {F : Type*} [Field F] [DecidableEq F]
    (hF : (2:F)≠0) {u v : F} (hu : u≠0)
    (hn : (curve F).toAffine.Nonsingular u v) :
    xCoord (Point.some u v hn + T₀ hF) = -1/u := by
  let e := (curve F).toAffine
  have hv := (literal_equation u v).mp hn.1
  let hT := nonsing_of_equation hF (show (0:F)^2=0^3-0 by ring)
  have hbr : ¬(u=0 ∧ v=e.negY 0 0) := fun h => hu h.1
  change xCoord (Point.some u v hn + Point.some 0 0 hT) = -1/u
  rw [Point.add_some hbr]
  change e.addX u 0 (e.slope u 0 v 0) = -1/u
  rw [slope_of_X_ne hu,sub_zero,sub_zero,literal_addX,sub_zero,div_pow,hv]
  field_simp [hu] <;> ring

section Translation
variable {k : Type*} [Field k] [DecidableEq (FunctionField k)]

/-- The actual x-coefficient involution by the fixed stock T₀
acts on the generic scalar's abscissa by the same -1/u formula. -/
private theorem translated_scalar_abscissa
    (h2 : (2:k)≠0) (i : k) (hi : i^2= -1) (a b : ℤ) (hodd : Odd (a+b))
    (u v : FunctionField k) (hn : (curve (FunctionField k)).toAffine.Nonsingular u v)
    (hGen : gaussian (function_two_ne k h2) (constGeneric k i)
      (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi)
      a b (genericPoint k h2) = Point.some u v hn)
    (hu : u≠0) :
    translateFrac k u = -1/u := by
  let hF := function_two_ne k h2
  let j := constGeneric k i
  let hj : j^2 = -1 := by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi
  let G := gaussian hF j hj a b
  let F := coordinateHom (translateFrac k) hF
  let P := genericPoint k h2
  let Q : WP (FunctionField k) := Point.some u v hn
  have hG : G P = Q := hGen
  have hFpt : F P = P + T₀ hF := translate_generic_point k h2
  have hT : G (T₀ hF) = T₀ hF := odd_scalar_T₀ hF j hj a b hodd
  have hc : F (G P) = G (F P) :=
    coordinate_gaussian (translateFrac k) hF hF j j hj hj (translate_fraction_const k i) a b P
  have hs : F Q = Q + T₀ hF := by
    calc
      _ = F (G P) := congrArg F hG.symm
      _ = G (F P) := hc
      _ = _ := by rw [hFpt,map_add,hG,hT]
  have e := congrArg xCoord hs
  change translateFrac k u = xCoord (Point.some u v hn + T₀ hF) at e
  exact e.trans (translate_T₀_x hF hu hn)

end Translation

private def polyImage (k : Type*) [Field k] : k[X] →+* FunctionField k :=
  (fractionMap k).comp (AdjoinRoot.of (relation k))

/-- No perfectness or extraction of coefficient p-th roots is
needed. On the same literal chart, the (canonical, finite)
quotient with vanishing derivative, degree cap and actual
pole at the origin has abscissa d₁*X^p+d₀. -/
private theorem literal_affine_x_power {k : Type*} [Field k] {p : ℕ} [CharP k p] (hp : 0 < p)
    (R : RatFunc k) (u : FunctionField k)
    (hRat : u = fractionMap k (AdjoinRoot.of (relation k) R.num) /
        fractionMap k (AdjoinRoot.of (relation k) R.denom))
    (hDeriv : R.num.derivative * R.denom - R.num * R.denom.derivative = 0)
    (hCap : max R.num.natDegree R.denom.natDegree ≤ p)
    (hPole : R.denom.natDegree < R.num.natDegree) :
    ∃ d₁ d₀ : k, d₁ ≠ 0 ∧
      u = constGeneric k d₁ * (xGeneric k)^p + constGeneric k d₀ := by
  obtain ⟨hA,hB,h₁,h₀⟩ := pole_forces_affine_frobenius hp (RatFunc.isCoprime_num_denom R)
    (RatFunc.denom_ne_zero R) hPole ((le_max_left _ _).trans hCap) (sub_eq_zero.mp hDeriv)
  let f := polyImage k
  have hC (s : k) : f (C s) = constGeneric k s := rfl
  have hX : f (X : k[X]) = xGeneric k := rfl
  let a := R.num.coeff p
  let b := R.num.coeff 0
  let c := R.denom.coeff 0
  refine ⟨a/c,b/c,div_ne_zero h₁ h₀,?_⟩
  calc
    u = f R.num / f R.denom := hRat
    _ = (constGeneric k b + constGeneric k a * (xGeneric k)^p) / constGeneric k c := by
      rw [hA,hB,map_add,map_mul,map_pow,hC,hC,hC,hX]
    _ = _ := by
      simp only [map_div₀,div_eq_mul_inv]
      ring

private theorem polynomial_injects (k : Type*) [Field k] :
    Function.Injective (polyImage k) := by
  have hm : (relation k).Monic := monic_X_pow_sub_C _ (by decide)
  have hd : 0 < (relation k).degree := by
    rw [show (relation k).degree = 2 from degree_X_pow_sub_C (by decide : 0 < 2) _]
    decide
  exact (fractionMap_injective k).comp (AdjoinRoot.of.injective_of_monic_of_degree_pos hm hd)

private theorem affine_power_nonzero {k : Type*} [Field k] {p : ℕ} (hp : 0 < p)
    {d₁ d₀ : k} (hd : d₁ ≠ 0) {u : FunctionField k}
    (hu : u = constGeneric k d₁ * (xGeneric k)^p + constGeneric k d₀) : u ≠ 0 := by
  intro hu0
  let f := polyImage k
  let Q : k[X] := C d₁ * X^p + C d₀
  have hC (s : k) : f (C s) = constGeneric k s := rfl
  have hX : f (X : k[X]) = xGeneric k := rfl
  have hQ : f Q = 0 := by
    change f (C d₁ * X^p + C d₀) = 0
    simpa only [map_add,map_mul,map_pow,hC,hX] using hu.symm.trans hu0
  have hz : Q = 0 := polynomial_injects k (hQ.trans (map_zero f).symm)
  have hcoeff := congrArg (fun Q : k[X] => Q.coeff p) hz
  exact hd (by simpa [Q,coeff_add,coeff_C_mul_X_pow,coeff_C,hp.ne',Ne.symm hp.ne'] using hcoeff)

/-- The fixed actual T₀ translation supplies the reciprocal identity
for the same signed generic abscissa. It forces zero intercept and
scale ±1 directly on X^p, with no coefficient roots. This does not
choose the sign or assert equality of the ordinates. -/
private theorem reciprocal_forces_x_power_sign {k : Type*} [Field k] {p : ℕ}
    (hp : 0 < p) (hodd : Odd p) {d₁ d₀ : k} (hd : d₁ ≠ 0) {u : FunctionField k}
    (hu : u = constGeneric k d₁ * (xGeneric k)^p + constGeneric k d₀)
    (hRecip : translateFrac k u = -1/u) :
    u = (xGeneric k)^p ∨ u = -(xGeneric k)^p := by
  let F := FunctionField k
  let x := xGeneric k
  let Z := x^p
  let a := constGeneric k d₁
  let b := constGeneric k d₀
  have hZ : Z ≠ 0 := pow_ne_zero p (xGeneric_ne k)
  have hu0 := affine_power_nonzero hp hd hu
  have ht : translateFrac k u = a * (-1/Z) + b := by
    rw [hu,map_add,map_mul,map_pow,translate_fraction_const,translate_fraction_x,
      translate_fraction_const,div_pow,hodd.neg_one_pow]
  have hmul : (a * (-1/Z) + b) * (a * Z + b) = (-1:F) := by
    have e := (eq_div_iff hu0).mp (ht.symm.trans hRecip)
    simpa only [hu] using e
  have hcleared : Z * (a * (-1/Z) + b) = -a + b*Z := by
    field_simp [hZ] <;> ring
  have hpoly := congrArg (fun z : F => Z*z) hmul
  change Z*((a*(-1/Z)+b)*(a*Z+b))=Z*(-1) at hpoly
  rw [←mul_assoc,hcleared,mul_neg_one] at hpoly
  let P : k[X] := C (d₁*d₀)*X^(p+p)+C (d₀^2-d₁^2+1)*X^p-C (d₁*d₀)
  let f := polyImage k
  have hC (s : k) : f (C s) = constGeneric k s := rfl
  have hX : f (X : k[X]) = x := rfl
  have hP : f P = 0 := by
    change f (C (d₁*d₀)*X^(p+p)+C (d₀^2-d₁^2+1)*X^p-C (d₁*d₀))=0
    simp only [map_sub,map_add,map_mul,map_pow,hC,hX,pow_add,map_one]
    change a*b*(Z*Z)+(b^2-a^2+1)*Z-a*b=0
    linear_combination hpoly
  have hP0 : P=0 := polynomial_injects k (hP.trans (map_zero f).symm)
  have h₁' : (p+p : ℕ) ≠ p := by omega
  have h₂' : (p+p : ℕ) ≠ 0 := by omega
  have htop := congrArg (fun P : k[X] => P.coeff (p+p)) hP0
  have hmid := congrArg (fun P : k[X] => P.coeff p) hP0
  have hab : d₁*d₀=0 := by
    simpa [P,coeff_sub,coeff_add,coeff_C_mul_X_pow,coeff_C,h₁',h₂',Ne.symm h₁',Ne.symm h₂'] using htop
  have hb : d₀=0 := (mul_eq_zero.mp hab).resolve_left hd
  have hmid' : d₀^2-d₁^2+1=0 := by
    simpa [P,coeff_sub,coeff_add,coeff_C_mul_X_pow,coeff_C,hp.ne',Ne.symm hp.ne',
      h₁',Ne.symm h₁'] using hmid
  have hs : d₁^2=1 := by
    rw [hb,zero_pow (by decide : (2:ℕ) ≠ 0)] at hmid'
    linear_combination -hmid'
  have hs' : (d₁-1)*(d₁+1)=0 := by linear_combination hs
  rcases mul_eq_zero.mp hs' with h|h
  · have ha : d₁=1 := sub_eq_zero.mp h
    exact Or.inl (by simpa only [ha,hb,map_one,map_zero,one_mul,add_zero] using hu)
  · have ha : d₁= -1 := by linear_combination h
    exact Or.inr (by simpa only [ha,hb,map_neg,map_one,map_zero,neg_one_mul,add_zero] using hu)

private theorem power_sign {F : Type*} [Field F] {x y : F} (h : x ^ 2 = y ^ 2) :
    x = y ∨ x = -y := by
  have h' : (x-y)*(x+y)=0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h₁|h₂
  · exact Or.inl (sub_eq_zero.mp h₁)
  · exact Or.inr (by linear_combination h₂)

variable {k : Type*} [Field k] [DecidableEq (FunctionField k)]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- The actual origin-pole theorem applies on the literal same residual
generic point and canonical RatFunc. Derivative zero and the transported
cap give pure p-power coordinate branches of that same scalar. No
assumed pole, perfectness, phase or equality of endomorphisms. -/
theorem actual_scalar_pure_power_shapes
    (h2 : (2 : k) ≠ 0) (i : k) (hi : i ^ 2 = -1)
    (a b : ℤ) (hN : a ^ 2 + b ^ 2 = (p : ℤ)) (hOdd : Odd (p : ℤ))
    (R : RatFunc k)
    (u v : FunctionField k) (hn : (curve (FunctionField k)).toAffine.Nonsingular u v)
    (hGen : gaussian (function_two_ne k h2) (constGeneric k i)
      (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi)
      a b (genericPoint k h2) = Point.some u v hn)
    (hRat : u = fractionMap k (AdjoinRoot.of (relation k) R.num) /
        fractionMap k (AdjoinRoot.of (relation k) R.denom))
    (hCap : max R.num.natDegree R.denom.natDegree ≤ p)
    (hDeriv : R.num.derivative * R.denom - R.num * R.denom.derivative = 0) :
    let Xp := (xGeneric k)^p
    let Yp := (yGeneric k)^p
    let j := constGeneric k i
    (u=Xp ∧ (v=Yp ∨ v= -Yp)) ∨
      (u= -Xp ∧ (v=j*Yp ∨ v= -(j*Yp))) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp2 : p ≠ 2 := by
    intro e
    obtain ⟨n,hn⟩ := hOdd
    rw [e] at hn
    norm_num at hn <;> omega
  have hOddN : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hPole := actual_origin_is_a_pole h2 i hi a b R.num R.denom
    (RatFunc.denom_ne_zero R) u v hn hGen hRat
  obtain ⟨α,β,hα,hAff⟩ := literal_affine_x_power (p := p) hp R u hRat hDeriv hCap hPole
  have hu0 := affine_power_nonzero hp hα hAff
  have hRecip := translated_scalar_abscissa h2 i hi a b (norm_odd hN hOdd) u v hn hGen hu0
  have hX := reciprocal_forces_x_power_sign hp hOddN hα hAff hRecip
  let F := FunctionField k
  let Xp := (xGeneric k)^p
  let Yp := (yGeneric k)^p
  let j := constGeneric k i
  let f := constGeneric k
  letI : CharP F p := ⟨fun n => by
    have e : (n:F)=0 ↔ (n:k)=0 := by
      rw [← map_natCast f n, ← map_zero f, f.injective.eq_iff]
    exact e.trans (CharP.cast_eq_zero_iff k p n)⟩
  have hCube : Yp^2=Xp^3-Xp := by
    have e := congrArg (frobenius F p) (equation_generic k)
    simpa only [map_pow,map_sub,frobenius_def,Xp,Yp] using e
  have hV := (literal_equation u v).mp hn.1
  change (u=Xp ∧ (v=Yp ∨ v= -Yp)) ∨ (u= -Xp ∧ (v=j*Yp ∨ v= -(j*Yp)))
  rcases hX with hx | hx
  · exact Or.inl ⟨hx,power_sign (by rw [hV,hx,hCube])⟩
  · have hj : j^2 = -1 := by
      simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi
    refine Or.inr ⟨hx,power_sign ?_⟩
    rw [hV,hx,mul_pow,hj,hCube]
    ring

end ActualGaussianWeberActualOriginPurePowers318
