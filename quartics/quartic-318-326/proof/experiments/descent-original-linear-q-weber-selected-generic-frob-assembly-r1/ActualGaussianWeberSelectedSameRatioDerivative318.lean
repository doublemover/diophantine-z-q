module
public import ActualGaussianWeberAcceptedMixedFirstJet318
public import ActualGaussianWeberStationaryScalar318
public import ActualGaussianWeberSameRatioJetCross318
public import ActualGaussianWeberSelectedGaussianPrime318
public import Mathlib.FieldTheory.RatFunc.Basic
public import ActualGaussianWeberScalarOnArc318
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public section
noncomputable section

namespace ActualGaussianWeberSelectedSameRatioDerivative318

open IsLocalRing Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberValuedKernelChart318
open ActualGaussianWeberQuadraticGenericChart318 ActualGaussianWeberGaussLocalization318
open ActualGaussianWeberTranslationFunctionField318 ActualGaussianWeberOddNormGeneric318
open ActualGaussianWeberOriginJet318 ActualGaussianWeberStationaryScalar318
open ActualGaussianWeberPowerSeriesArc318 ActualGaussianWeberSameRatioJetCross318
open ActualGaussianWeberScalarOnArc318 ActualGaussianWeberAcceptedMixedFirstJet318
open ActualGaussianWeberQuarterTurn318 ActualGaussianWeberGaussianScalarSpecialization318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberPlaceEquivariance318

variable {k : Type*} [Field k]

/-- The literal abscissa embedding of the exact chart function field. -/
private def xRing : k[X] →+* FunctionField k :=
  (fractionMap k).comp (AdjoinRoot.of (relation k))

private theorem eval_at_generic (P : k[X]) :
    P.eval₂ (constGeneric k) (xGeneric k)=xRing (k:=k) P := by
  induction P using Polynomial.induction_on' with
  | add A B hA hB => rw [eval₂_add,map_add,hA,hB]
  | monomial n a =>
    rw [←C_mul_X_pow_eq_monomial,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X,map_mul,map_pow] <;> rfl

private theorem xRing_injective : Function.Injective (xRing (k:=k)) := by
  have hm : (relation k).Monic := monic_X_pow_sub_C _ (by decide)
  have hdeg : 0 < (relation k).degree := by
    rw [show (relation k).degree=2 from degree_X_pow_sub_C (by decide : 0<2) _]
    decide
  intro A B h
  have hImage : fractionMap k (AdjoinRoot.of (relation k) A)=
      fractionMap k (AdjoinRoot.of (relation k) B) := h
  exact AdjoinRoot.of.injective_of_monic_of_degree_pos hm hdeg
    (fractionMap_injective k hImage)

private theorem generic_ordinate_ne : yGeneric k ≠ 0 := by
  intro h
  have hC : (ActualGaussianWeberTranslationChart318.yChart k : Chart k)=0 := fractionMap_injective k
    (h.trans (map_zero (fractionMap k)).symm)
  have hE : (element (0:k[X]) 1 : Chart k)=element 0 0 := by
    simpa only [element,ActualGaussianWeberTranslationChart318.yChart,map_zero,map_one,
      zero_mul,zero_add,one_mul] using hC
  exact one_ne_zero (element_coefficients hE).2

private theorem abscissa_eq {F : Type*} [Field F] {x y z w : F}
    {h : (curve F).toAffine.Nonsingular x y} {j : (curve F).toAffine.Nonsingular z w}
    (e : Point.some x y h=Point.some z w j) : x=z :=
  congrArg (fun P : WP F => match P with | .zero => 0 | .some u _ _ => u) e

variable [DecidableEq (FunctionField k)]

/-- The actual selected Gaussian scalar has stationary rational
abscissa, as an identity over the original coefficient/residue field k.
Its single finite probe is the generic point itself, viewed as a
constant of the Laurent field over k(E), not a finite-field point.
No degree, separability, unit, pole at infinity, algebraic closure or
pointwise density assumption enters. -/
theorem chosen_cross_on_canonical_ratio (h2 : (2:k) ≠ 0) (i : k) (hi : i^2= -1)
    (a b : ℤ) (hSelected : (a:k)+(b:k)*i=0) (R : RatFunc k)
    (u v : FunctionField k) (huv : (curve (FunctionField k)).toAffine.Nonsingular u v)
    (hGen : gaussian (function_two_ne k h2) (constGeneric k i)
      (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi)
      a b (genericPoint k h2)=Point.some u v huv)
    (hRat : u=fractionMap k (AdjoinRoot.of (relation k) R.num) /
      fractionMap k (AdjoinRoot.of (relation k) R.denom)) :
    R.num.derivative*R.denom-R.num*R.denom.derivative=0 := by
  classical
  let A := R.num
  let B := R.denom
  have hB : B≠0 := RatFunc.denom_ne_zero R
  let L := FunctionField k
  let e : k→+*L := constGeneric k
  let x := xGeneric k
  let y := yGeneric k
  let F := FormalField L
  let V := FormalValuation L
  let t := parameter L
  let f := constField L
  let c := constVal L
  let reduce := constantTerm L
  let m := f.comp e
  let hL := function_two_ne k h2
  let hF := formal_two_ne L hL
  let hR := formal_residue_two_ne L hL
  let iL := e i
  have hiL : iL^2= -1 := by simpa only [map_pow,map_neg,map_one] using congrArg e hi
  let j := c iL
  have hj : j^2= -1 := by
    change (c iL)^2=(-1:V)
    calc
      _ = c (iL^2) := (map_pow c iL 2).symm
      _ = c (-1) := congrArg c hiL
      _ = -(c 1) := map_neg c (1:L)
      _ = _ := congrArg (fun z : V => -z) (map_one c)
  let hjF := chosen_square_generic V j hj
  let G := gaussian hF (f iL) hjF a b
  have hSL : (a:L)+(b:L)*iL=0 := by
    simpa only [map_add,map_mul,map_zero,map_intCast] using congrArg e hSelected
  have hSel : (a:ResidueField V)+(b:ResidueField V)*residue V j=0 := by
    apply (residueFormal L).injective
    have hjr : residueFormal L (residue V j)=iL := by
      change residueFormal L (residue (FormalValuation L) (constVal L iL))=iL
      exact residueFormal_const L iL
    simpa only [map_add,map_mul,map_zero,map_intCast,hjr] using hSL
  obtain ⟨pX,pY,hp,hP,hT⟩ := formal_origin_arc L hL
  let P := Point.some pX pY hp
  have hPar : tCoord P=V.subtype t := hT
  let Pu : scaledOrigin V hF hR t (parameter_small L) :=
    ⟨P,⟨⟨hP,1,by rw [mul_one]; exact hPar⟩⟩⟩
  have hsP : specialize V hR (G P)=Point.zero ∧
      ∃ d : V, tCoord (G P)=V.subtype (t^2*d) :=
    selected_scalar_stationary V hF hR t (parameter_small L) (parameter_ne L)
      (principal L) j hj a b hSel Pu

  let Q := genericPoint k h2
  let M := coordinateHom f hF
  let hn := nonsing_of_equation hL (equation_generic k)
  let hQ := mapped_nonsingular f hF hn
  have hMQ : M Q=Point.some (V.subtype (c x)) (V.subtype (c y)) hQ :=
    point_some f hF hn
  obtain ⟨X,Y,hXY,hOuter,Cx,hX⟩ :=
    mixed_abscissa_expansion V hR P (c x) (c y) t hQ hP hPar
  have hOuter' : P+M Q=Point.some (V.subtype X) (V.subtype Y) hXY := by
    rw [hMQ]; exact hOuter
  have hX' : X=c x+t*c (2*y)+t^2*Cx := by rw [hX,map_mul,map_ofNat]; ring
  have hX0 : reduce X=x := by rw [hX']; exact linear_arc_constant x (2*y) Cx

  -- Evaluating after this actual mixed input is already faithful
  -- from its constant coefficient X, unlike a residue point.
  have hEv : Function.Injective (eval₂RingHom m (V.subtype X)) := by
    let g := eval₂RingHom (c.comp e) X
    have hc : reduce.comp (c.comp e)=e := by
      apply RingHom.ext
      intro w
      change constantTerm L (constVal L (e w))=e w
      exact constantTerm_const L (e w)
    intro U W h
    have hV : g U=g W := by
      apply V.subtype_injective
      change V.subtype (U.eval₂ (c.comp e) X)=V.subtype (W.eval₂ (c.comp e) X)
      rw [hom_eval₂,hom_eval₂]
      exact h
    have hL' := congrArg reduce hV
    change reduce (U.eval₂ (c.comp e) X)=reduce (W.eval₂ (c.comp e) X) at hL'
    rw [hom_eval₂,hom_eval₂,hc,hX0,eval_at_generic,eval_at_generic] at hL'
    exact xRing_injective hL'

  have hEquation := (literal_equation _ _).mp hXY.1
  obtain ⟨Y',hY',hEval⟩ := scalar_rational_x_on_arc m h2 hF i hi a b A B
    (V.subtype X) (V.subtype Y) hEquation hEv u v huv hGen hRat
  let R := A.eval₂ m (V.subtype X)/B.eval₂ m (V.subtype X)
  have hE : G (P+M Q)=Point.some R Y' hY' := by
    calc
      _ = G (Point.some (V.subtype X) (V.subtype Y) (nonsing_of_equation hF hEquation)) :=
        congrArg G hOuter'
      _ = _ := hEval
  let hW := mapped_nonsingular f hF huv
  have hGQ : G (M Q)=Point.some (V.subtype (c u)) (V.subtype (c v)) hW := by
    have hC := coordinate_gaussian f hL hF iL (f iL) hiL hjF rfl a b Q
    change M (gaussian hL iL hiL a b Q)=G (M Q) at hC
    have hQ' : gaussian hL iL hiL a b Q=Point.some u v huv := hGen
    rw [hQ'] at hC
    exact hC.symm.trans (point_some f hF huv)
  obtain ⟨Z,W,hZW,hInner,d,hZ⟩ :=
    stationary_mixed_abscissa V hR (G P) (c u) (c v) t hW hsP.1 hsP.2
  have hI : G (P+M Q)=Point.some (V.subtype Z) (V.subtype W) hZW := by
    rw [map_add,hGQ]
    exact hInner
  have hEqRat : V.subtype Z=R := abscissa_eq (hI.symm.trans hE)

  have hDen : (B.map e).eval x ≠ 0 := by
    rw [eval_map,eval_at_generic]
    intro hh
    exact hB (xRing_injective (hh.trans (map_zero (xRing (k:=k))).symm))
  have hJet := cross_from_same_germ (A.map e) (B.map e) x (2*y) u
    (mul_ne_zero hL generic_ordinate_ne) hDen X Z Cx d hX' hZ (by
      rw [eval₂_map,eval₂_map]
      exact hEqRat)
  let D := A.derivative*B-A*B.derivative
  have hD : (D.map e).eval x=0 := by
    simpa only [D,Polynomial.map_sub,Polynomial.map_mul,Polynomial.derivative_map] using hJet
  have hDD : xRing (k:=k) D=0 := by
    rw [eval_map,eval_at_generic] at hD
    exact hD
  exact xRing_injective (hDD.trans (map_zero (xRing (k:=k))).symm)

section ActualBase

open ActualGaussianWeberSelectedGaussianPrime318
attribute [local instance] Classical.decEq

/-- Actual normalized cross derivative on the literal selected base
residue. The selected coefficient is recovered from its checked
Gaussian residue ideal, not supplied as an extra stationarity axiom.
The only point equality and ratio are the exact descriptor fields. -/
theorem actual_selected_cross_of_descriptor {p : ℕ} [Fact p.Prime]
    (a b : ℤ) (hN : a^2+b^2=(p:ℤ))
    (h₂ : (2:ResidueField (BasePlace (rootOf (p:=p) a b) (rootOf_sq (p:=p) a b hN))) ≠ 0) :
    let j := rootOf (p:=p) a b
    let hj := rootOf_sq (p:=p) a b hN
    let V := BasePlace j hj
    let k := ResidueField V
    let i := integralI j hj
    let ι := residue V i
    ∀ (R : RatFunc k) (u v : FunctionField k)
      (hn : (curve (FunctionField k)).toAffine.Nonsingular u v),
      gaussian (function_two_ne k h₂) (constGeneric k ι)
        (by
          simpa only [map_pow,map_neg,map_one] using
            congrArg (constGeneric k) (chosen_square_residue V i (integralI_sq j hj)))
        a b (genericPoint k h₂)=Point.some u v hn →
      u=fractionMap k (AdjoinRoot.of (relation k) R.num) /
        fractionMap k (AdjoinRoot.of (relation k) R.denom) →
      R.num.derivative*R.denom-R.num*R.denom.derivative=0 := by
  dsimp only
  let j := rootOf (p:=p) a b
  let hj := rootOf_sq (p:=p) a b hN
  let V := BasePlace j hj
  let i := integralI j hj
  let ι := residue V i
  intro R u v hn hGen hRat
  have hSelected : (a:ResidueField V)+(b:ResidueField V)*ι=0 :=
    selected_zero_in_residue j hj a b (rootOf_selected (p:=p) a b hN)
  exact chosen_cross_on_canonical_ratio h₂ ι (chosen_square_residue V i (integralI_sq j hj))
    a b hSelected R u v hn hGen hRat

end ActualBase

end ActualGaussianWeberSelectedSameRatioDerivative318
