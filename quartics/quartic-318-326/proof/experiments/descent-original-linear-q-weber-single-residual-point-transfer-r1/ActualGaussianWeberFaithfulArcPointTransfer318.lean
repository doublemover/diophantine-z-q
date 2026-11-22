module
public import ActualGaussianWeberArcFunctionEmbedding318
public import ActualGaussianWeberPowerSeriesArc318
public import ActualGaussianWeberValuedPolynomialPole318
public import ActualGaussianWeberStockReductionAdd318
public import ActualGaussianWeberOddNormGeneric318
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.LinearCombination
public section
noncomputable section

namespace ActualGaussianWeberFaithfulArcPointTransfer318

open IsLocalRing Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberOddNormGeneric318
open ActualGaussianWeberGaussLocalization318 ActualGaussianWeberTranslationFunctionField318
open ActualGaussianWeberArcFunctionEmbedding318 ActualGaussianWeberPowerSeriesArc318
open ActualGaussianWeberValuedPolynomialPole318 ActualGaussianWeberValuedKernelChart318
open ActualGaussianWeberReductionCoordinates318 ActualGaussianWeberStockReductionAdd318
open ActualGaussianWeberMixedStockCoordinates318 ActualGaussianWeberMixedValuedData318
open ActualGaussianWeberGaussianScalarSpecialization318

attribute [local instance] Classical.decEq

theorem charP_along {K L : Type*} [Field K] [Field L]
    (f : K→+*L) (p : ℕ) [CharP K p] : CharP L p := by
  refine ⟨fun n => ?_⟩
  have h : (n:L)=0 ↔ (n:K)=0 := by
    rw [←map_natCast f n,←map_zero f,f.injective.eq_iff]
  exact h.trans (CharP.cast_eq_zero_iff K p n)

private def xOf {K : Type*} [Field K] (P : WP K) : K :=
  match P with | .zero => 0 | .some x _ _ => x

private def yOf {K : Type*} [Field K] (P : WP K) : K :=
  match P with | .zero => 0 | .some _ y _ => y

private theorem coordinate_injective {K L : Type*} [Field K] [Field L]
    [DecidableEq K] [DecidableEq L]
    (f : K→+*L) (hL : (2:L)≠0) : Function.Injective (coordinateHom f hL) := by
  intro P Q h
  change onCurvePoint f hL P=onCurvePoint f hL Q at h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y hn =>
      rw [point_some f hL hn] at h
      exact False.elim (Point.some_ne_zero _ h.symm)
  | some x y hn =>
    rw [point_some f hL hn] at h
    cases Q with
    | zero => exact False.elim (Point.some_ne_zero _ h)
    | some z w hq =>
      rw [point_some f hL hq] at h
      exact some_congr (f.injective (congrArg xOf h)) (f.injective (congrArg yOf h))

variable {p : ℕ} [Fact p.Prime]

/-- Frobenius is the literal coordinate p-power. It commutes with an
arbitrary ring embedding in characteristic p, not only with a map
whose target coefficients are individually fixed. -/
theorem coordinate_frobenius {K L : Type*} [Field K] [Field L]
    [DecidableEq K] [DecidableEq L]
    [CharP K p] [CharP L p] (f : K→+*L) (hK : (2:K)≠0) (hL : (2:L)≠0)
    (P : WP K) :
    coordinateHom f hL (coordinateHom (frobenius K p) hK P)=
      coordinateHom (frobenius L p) hL (coordinateHom f hL P) := by
  change onCurvePoint f hL (onCurvePoint (frobenius K p) hK P)=
    onCurvePoint (frobenius L p) hL (onCurvePoint f hL P)
  cases P with
  | zero => rfl
  | some x y hn =>
    simp only [point_some]
    exact some_congr (map_pow f x p) (map_pow f y p)

private theorem eval_restrict {K L F : Type*} [Field K] [Field L] [Field F]
    (f : K→+*L) (g : L→+*F) (x : F)
    (h : Function.Injective (eval₂RingHom g x)) :
    Function.Injective (eval₂RingHom (g.comp f) x) := by
  intro A B hAB
  apply Polynomial.map_injective f f.injective
  apply h
  change (A.map f).eval₂ g x=(B.map f).eval₂ g x
  rw [eval₂_map,eval₂_map]
  exact hAB

private theorem residue_formal_apply (K : Type*) [Field K] (z : FormalValuation K) :
    residueFormal K (residue (FormalValuation K) z)=constantTerm K z := by
  change ResidueField.lift (constantTerm K) (residue (FormalValuation K) z)=constantTerm K z
  exact ResidueField.lift_residue_apply _ _

/-- The actual translate by the same formal origin arc admits a
faithful evaluation at its abscissa even at residual 2-torsion. If it
were constant, the cubic and the actual residue of the ordinate
force both coordinates to be constant, contradicting cancellation. -/
theorem translated_arc_faithful {K : Type*} [Field K] [DecidableEq K] (hK : (2:K)≠0)
    (T : WP (FormalField K))
    (hT : specialize (FormalValuation K) (formal_residue_two_ne K hK) T=Point.zero)
    (hTne : T≠Point.zero)
    (x y : K) (hn : (curve K).toAffine.Nonsingular x y) :
    ∃ X Y : FormalValuation K,
      ∃ hXY : (curve (FormalField K)).toAffine.Nonsingular
        ((FormalValuation K).subtype X) ((FormalValuation K).subtype Y),
        T + coordinateHom (constField K) (formal_two_ne K hK) (Point.some x y hn)=
          Point.some ((FormalValuation K).subtype X) ((FormalValuation K).subtype Y) hXY ∧
        Function.Injective (eval₂RingHom (constField K) ((FormalValuation K).subtype X)) := by
  let V := FormalValuation K
  let c := constVal K
  let r := constantTerm K
  let e := constField K
  let hF := formal_two_ne K hK
  let hR := formal_residue_two_ne K hK
  let hQ := mapped_nonsingular e hF hn
  let Q := Point.some (V.subtype (c x)) (V.subtype (c y)) hQ
  have hQ' : coordinateHom e hF (Point.some x y hn)=Q := point_some e hF hn
  obtain ⟨D⟩ := from_kernel V hR T hT
  obtain ⟨U,hU,hAdd⟩ := mixed_stock_coordinates V hR T (c x) (c y) hQ hT hTne D
  let X := U.X
  let Y := U.Y
  have hAdd' : T+Q=Point.some (V.subtype X) (V.subtype Y) hU := hAdd
  obtain ⟨hR₁,hR₁e⟩ := reduction_through_coordinates V hR hQ (c x) (c y) rfl rfl
  obtain ⟨hR₂,hR₂e⟩ := reduction_through_coordinates V hR hU X Y rfl rfl
  have hRed : Point.some (residue V X) (residue V Y) hR₂=
      Point.some (residue V (c x)) (residue V (c y)) hR₁ := by
    calc
      _ = specialize V hR (Point.some (V.subtype X) (V.subtype Y) hU) := hR₂e.symm
      _ = specialize V hR (T+Q) := congrArg (specialize V hR) hAdd'.symm
      _ = specialize V hR Q := by
        rw [specialize_add V hF hR T Q,hT] <;> exact zero_add _
      _ = _ := hR₁e
  have hxR : residue V X=residue V (c x) := congrArg xOf hRed
  have hyR : residue V Y=residue V (c y) := congrArg yOf hRed
  have hxK : r X=x :=
    ((residue_formal_apply K X).symm.trans (congrArg (residueFormal K) hxR)).trans
      (residueFormal_const K x)
  have hyK : r Y=y :=
    ((residue_formal_apply K Y).symm.trans (congrArg (residueFormal K) hyR)).trans
      (residueFormal_const K y)
  have hNonconstant : X≠c (r X) := by
    intro he
    have hX : X=c x := he.trans (congrArg c hxK)
    have hCurve := equation_in_subring V X Y ((literal_equation _ _).mp hU.1)
    have hEq : Y^2=(c y)^2 := by
      rw [hCurve,hX]
      have h := congrArg c ((literal_equation x y).mp hn.1)
      simpa only [map_pow,map_sub] using h.symm
    have hProd : (Y-c y)*(Y+c y)=0 := by linear_combination hEq
    have hY : Y=c y := by
      rcases mul_eq_zero.mp hProd with h | h
      · exact sub_eq_zero.mp h
      · have hSign : Y= -(c y) := by linear_combination h
        have hyy : y= -y := by
          calc
            y = r Y := hyK.symm
            _ = r (-(c y)) := congrArg r hSign
            _ = -(r (c y)) := map_neg r (c y)
            _ = -y := congrArg (fun z : K => -z) (constantTerm_const K y)
        exact hSign.trans ((congrArg c hyy).trans (map_neg c y)).symm
    have hSame : Point.some (V.subtype X) (V.subtype Y) hU=Q :=
      some_congr (congrArg V.subtype hX) (congrArg V.subtype hY)
    have hCancel : T+Q=(0:WP (FormalField K))+Q :=
      (hAdd'.trans hSame).trans (zero_add Q).symm
    exact hTne (add_right_cancel hCancel)
  have hConst : r.comp c=RingHom.id K := by
    apply RingHom.ext
    intro z
    change constantTerm K (constVal K z)=z
    exact constantTerm_const K z
  have hInj := eval_integral_arc_injective c r hConst X hNonconstant
  refine ⟨X,Y,hU,?_,?_⟩
  · exact (congrArg (fun A => T+A) hQ').trans hAdd'
  · intro A B h
    apply hInj
    change A.eval₂ c X=B.eval₂ c X
    apply V.subtype_injective
    rw [hom_eval₂,hom_eval₂]
    exact h

private theorem faithful_affine_comparison {K : Type*} [Field K] [CharP K p] [DecidableEq K]
    (f : ZMod p→+*K) (h₂ : (2:ZMod p)≠0) (hK : (2:K)≠0)
    (s : ZMod p) (hs : s^2= -1) (a b : ℤ)
    (hGeneric :
      let h := function_two_ne (ZMod p) h₂
      let c := constGeneric (ZMod p) s
      let hc : c^2= -1 := by
        simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric (ZMod p)) hs
      letI : CharP (FunctionField (ZMod p)) p := charP_along (constGeneric (ZMod p)) p
      gaussian h c hc a b (genericPoint (ZMod p) h₂)=
        coordinateHom (frobenius (FunctionField (ZMod p)) p) h (genericPoint (ZMod p) h₂))
    (x y : K) (hn : (curve K).toAffine.Nonsingular x y)
    (hFaithful : Function.Injective (eval₂RingHom f x)) :
    let hf : (f s)^2= -1 := by
      simpa only [map_pow,map_neg,map_one] using congrArg f hs
    gaussian hK (f s) hf a b (Point.some x y hn)=
      coordinateHom (frobenius K p) hK (Point.some x y hn) := by
  let k := ZMod p
  let L := FunctionField k
  letI : CharP L p := charP_along (constGeneric k) p
  let hL := function_two_ne k h₂
  let j := constGeneric k s
  let hj : j^2= -1 := by
    simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hs
  let i := f s
  let hi : i^2= -1 := by
    simpa only [map_pow,map_neg,map_one] using congrArg f hs
  let he := (literal_equation x y).mp hn.1
  let g := arcEmbedding f x y he hFaithful
  let P := genericPoint k h₂
  let E := coordinateHom g hK
  have hJ : g j=i := arcEmbedding_const f x y he hFaithful s
  let hP := nonsing_of_equation hL (equation_generic k)
  have hImage : E P=Point.some x y hn := by
    change onCurvePoint g hK (Point.some (xGeneric k) (yGeneric k) hP)=_
    rw [point_some g hK hP]
    exact some_congr (arcEmbedding_x f x y he hFaithful) (arcEmbedding_y f x y he hFaithful)
  have hG : gaussian hL j hj a b P=coordinateHom (frobenius L p) hL P := hGeneric
  calc
    _ = gaussian hK i hi a b (E P) := congrArg (gaussian hK i hi a b) hImage.symm
    _ = E (gaussian hL j hj a b P) := (coordinate_gaussian g hL hK j i hj hi hJ a b P).symm
    _ = E (coordinateHom (frobenius L p) hL P) := congrArg E hG
    _ = coordinateHom (frobenius K p) hK (E P) := coordinate_frobenius g hL hK P
    _ = _ := congrArg (coordinateHom (frobenius K p) hK) hImage

/-- Specialize one generic identity to one prescribed stock point.
The two evaluations are the same formal origin and its translate
by this point. No density, number of rational points, ratio,
degree, or norm input enters. -/
theorem generic_identity_at_prescribed_point {K : Type*} [Field K] [CharP K p] [DecidableEq K]
    (f : ZMod p→+*K) (h₂ : (2:ZMod p)≠0) (hK : (2:K)≠0)
    (s : ZMod p) (hs : s^2= -1) (a b : ℤ)
    (hGeneric :
      let h := function_two_ne (ZMod p) h₂
      let c := constGeneric (ZMod p) s
      let hc : c^2= -1 := by
        simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric (ZMod p)) hs
      letI : CharP (FunctionField (ZMod p)) p := charP_along (constGeneric (ZMod p)) p
      gaussian h c hc a b (genericPoint (ZMod p) h₂)=
        coordinateHom (frobenius (FunctionField (ZMod p)) p) h (genericPoint (ZMod p) h₂))
    (P : WP K) :
    let hf : (f s)^2= -1 := by
      simpa only [map_pow,map_neg,map_one] using congrArg f hs
    gaussian hK (f s) hf a b P=coordinateHom (frobenius K p) hK P := by
  cases P with
  | zero => simp only [map_zero]
  | some x y hn =>
    let F := FormalField K
    let V := FormalValuation K
    let hF := formal_two_ne K hK
    let hR := formal_residue_two_ne K hK
    let e := constField K
    let m := e.comp f
    letI : CharP F p := charP_along e p
    let i := f s
    let ii := m s
    have hi : i^2= -1 := by
      simpa only [map_pow,map_neg,map_one] using congrArg f hs
    have hii : ii^2= -1 := by
      simpa only [map_pow,map_neg,map_one] using congrArg m hs
    let G := gaussian hF ii hii a b
    let H := coordinateHom (frobenius F p) hF
    let E := coordinateHom e hF
    let Q := E (Point.some x y hn)
    obtain ⟨tX,tY,hTn,hT₀,_⟩ := formal_origin_arc K hK
    let T := Point.some tX tY hTn
    have hT : specialize V hR T=Point.zero := hT₀
    have hTne : T≠Point.zero := Point.some_ne_zero _
    have hPole : tX∉V := (specialize_some_eq_zero V hR hTn).mp hT
    have hEvT : Function.Injective (eval₂RingHom m tX) := by
      change Function.Injective (eval₂RingHom (e.comp f) tX)
      exact eval_restrict f e tX (evaluation_at_pole_injective V (constVal K) hPole)
    have hAtT : G T=H T :=
      faithful_affine_comparison m h₂ hF s hs a b hGeneric tX tY hTn hEvT
    obtain ⟨X,Y,hU,hUe,hFaith⟩ := translated_arc_faithful hK T hT hTne x y hn
    have hMove : T+Q=Point.some (V.subtype X) (V.subtype Y) hU := hUe
    have hAtMoved : G (T+Q)=H (T+Q) := by
      rw [hMove]
      exact faithful_affine_comparison m h₂ hF s hs a b hGeneric
        (V.subtype X) (V.subtype Y) hU (eval_restrict f e (V.subtype X) hFaith)
    rw [map_add,map_add,hAtT] at hAtMoved
    have hAtQ : G Q=H Q := add_left_cancel hAtMoved
    apply coordinate_injective e hF
    have hE₁ : E (gaussian hK i hi a b (Point.some x y hn))=G Q :=
      coordinate_gaussian e hK hF i ii hi hii rfl a b (Point.some x y hn)
    have hE₂ : E (coordinateHom (frobenius K p) hK (Point.some x y hn))=H Q :=
      coordinate_frobenius e hK hF (Point.some x y hn)
    exact hE₁.trans (hAtQ.trans hE₂.symm)

end ActualGaussianWeberFaithfulArcPointTransfer318
