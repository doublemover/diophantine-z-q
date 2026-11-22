module
public import ActualGaussianWeberPrimaryProbe318
public import ActualGaussianWeberFixedXAffineHenselProbe318
public import ActualGaussianWeberPowerSeriesArc318
public import ActualGaussianWeberArcFunctionEmbedding318
public import ActualGaussianWeberOddNormGeneric318
public import ActualGaussianWeberStockReductionAdd318
public import Mathlib.Algebra.CharP.Frobenius
public section
noncomputable section

namespace ActualGaussianWeberPrimaryOneAffineProbe318

open IsLocalRing Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318
open ActualGaussianWeberStockCoordinateHom318 ActualGaussianWeberReductionCoordinates318
open ActualGaussianWeberStockReductionAdd318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberPowerSeriesArc318 ActualGaussianWeberPrimaryProbe318
open ActualGaussianWeberFixedXAffineHenselProbe318 ActualGaussianWeberArcFunctionEmbedding318
open ActualGaussianWeberQuadraticGenericChart318 ActualGaussianWeberGaussLocalization318
open ActualGaussianWeberTranslationFunctionField318 ActualGaussianWeberOddNormGeneric318
open ActualGaussianWeberGaussianScalarSpecialization318

inductive ProbeUnit where
  | id | minus | quarter | minusQuarter
  deriving DecidableEq

variable {R F : Type*} [CommRing R] [Field F]

@[expose] def unitX (e : ProbeUnit) (x : R) : R := match e with
  | .id | .minus => x
  | .quarter | .minusQuarter => -x

@[expose] def unitY (e : ProbeUnit) (i y : R) : R := match e with
  | .id => y
  | .minus => -y
  | .quarter => i*y
  | .minusQuarter => -(i*y)

private theorem map_unitX {S : Type*} [CommRing S] (g : R→+*S)
    (e : ProbeUnit) (x : R) : g (unitX e x)=unitX e (g x) := by
  cases e <;> simp only [unitX,map_neg]

private theorem map_unitY {S : Type*} [CommRing S] (g : R→+*S)
    (e : ProbeUnit) (i y : R) : g (unitY e i y)=unitY e (g i) (g y) := by
  cases e <;> simp only [unitY,map_neg,map_mul]

variable {k : Type*} [Field k]

private theorem actual_primary_fixes_probe [DecidableEq k]
    (h2 : (2:k) ≠ 0) (i : k) (hi : i^2= -1) (a b c d : ℤ)
    (ha : a=1-2*(c+d)) (hb : b=2*(c-d)) :
    gaussian h2 i hi a b (probe h2 i hi)=probe h2 i hi := by
  have hrot : turn h2 i hi (probe h2 i hi)=probe h2 (-i) (negative_i_square i hi) := by
    unfold probe
    rw [turn_some]
    exact ActualGaussianWeberStockCoordinateHom318.some_congr rfl (by linear_combination -hi)
  change a • probe h2 i hi+b • turn h2 i hi (probe h2 i hi)=_
  rw [hrot]
  exact primary_preserves_probe h2 i hi a b c d ha hb

variable {p : ℕ} [Fact p.Prime] [CharP k p] [DecidableEq (FunctionField k)]

/-- The four established generic coordinate branches are compared
at one faithful affine Hensel lift. Unlike the origin-plus-probe arc,
this uses X=i+t directly, so no mixed addition is needed here. -/
theorem primary_tag_from_one_affine_probe (h2 : (2:k)≠0)
    (i : k) (hi : i^2= -1) (hiFixed : i^p=i)
    (a b c d : ℤ) (ha : a=1-2*(c+d)) (hb : b=2*(c-d))
    (e : ProbeUnit) (u v : FunctionField k)
    (huv : (curve (FunctionField k)).toAffine.Nonsingular u v)
    (hGeneric : gaussian (function_two_ne k h2) (constGeneric k i)
      (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi)
      a b (genericPoint k h2)=Point.some u v huv)
    (hu : u=unitX e ((xGeneric k)^p))
    (hv : v=unitY e (constGeneric k i) ((yGeneric k)^p)) :
    e=ProbeUnit.id := by
  classical
  let L := FormalField k
  let V := FormalValuation k
  let t := parameter k
  let C := constVal k
  let f := constField k
  let hF := formal_two_ne k h2
  let hR := formal_residue_two_ne k h2
  let hG := function_two_ne k h2
  let j := C i
  have hj : j^2= -1 := by
    simpa only [j,map_pow,map_neg,map_one] using congrArg C hi
  let hjF := chosen_square_generic V j hj
  let jR := residue V j
  let hjR := chosen_square_residue V j hj
  let jG := constGeneric k i
  have hjG : jG^2= -1 := by simpa only [jG,map_pow,map_neg,map_one] using congrArg (constGeneric k) hi
  let rho := (residueFormal k).toRingHom
  let T := coordinateHom rho h2
  let red := T.comp (specializeHom V hF hR)
  let theta := rho.comp (residue V)
  have hC (x : k) : theta (C x)=x := residueFormal_const k x
  let GF := gaussian hF (V.subtype j) hjF a b
  let GR := gaussian hR jR hjR a b
  let G₀ := gaussian h2 i hi a b
  have red_finite (x y : V) (h : (curve L).toAffine.Nonsingular (V.subtype x) (V.subtype y)) :
      ∃ h' : (curve k).toAffine.Nonsingular (theta x) (theta y),
        red (Point.some (V.subtype x) (V.subtype y) h)=Point.some (theta x) (theta y) h' := by
    obtain ⟨hr,he⟩ := reduction_through_coordinates V hR h x y rfl rfl
    let hs := mapped_nonsingular rho h2 hr
    refine ⟨hs,?_⟩
    change T (specialize V hR (Point.some (V.subtype x) (V.subtype y) h))=_
    rw [he] <;> exact point_some rho h2 hr
  let X := C i+t
  obtain ⟨Y,hEq,hX0,hY0,hNon⟩ := fixed_x_lift h2 i (1-i)
    (probe_y_ne h2 i hi) (probe_equation i hi)
  have eqM : (V.subtype Y)^2=(V.subtype X)^3-V.subtype X := by
    simpa only [map_pow,map_sub] using congrArg V.subtype hEq
  let hXY := nonsing_of_equation hF eqM
  let M := Point.some (V.subtype X) (V.subtype Y) hXY
  let Q₀ := probe h2 i hi
  have hRead (w : V) : theta w = constantTerm k w := by
    change IsLocalRing.ResidueField.lift (constantTerm k) (residue V w)=constantTerm k w
    exact IsLocalRing.ResidueField.lift_residue_apply _ _
  have hθX : theta X=i := (hRead X).trans hX0
  have hθY : theta Y=1-i := (hRead Y).trans hY0
  obtain ⟨hMbar,hMr⟩ := red_finite X Y hXY
  have hRedM : red M=Q₀ :=
    hMr.trans (ActualGaussianWeberStockCoordinateHom318.some_congr hθX hθY)
  have hSplit : (constantTerm k).comp C=RingHom.id k := RingHom.ext (constantTerm_const k)
  have hEval : Function.Injective (eval₂RingHom f (V.subtype X)) := by
    have H := eval_integral_arc_injective C (constantTerm k) hSplit X hNon
    intro A B ha
    apply H
    apply V.subtype_injective
    change V.subtype (A.eval₂ C X)=V.subtype (B.eval₂ C X)
    rw [hom_eval₂,hom_eval₂]
    exact ha
  let m := arcEmbedding f (V.subtype X) (V.subtype Y) eqM hEval
  let E := coordinateHom m hF
  have hmX : m (xGeneric k)=V.subtype X := arcEmbedding_x f _ _ eqM hEval
  have hmY : m (yGeneric k)=V.subtype Y := arcEmbedding_y f _ _ eqM hEval
  have hmj : m jG=V.subtype j := arcEmbedding_const f _ _ eqM hEval i
  have hE : E (genericPoint k h2)=M := by
    change onCurvePoint m hF (Point.some (xGeneric k) (yGeneric k)
      (nonsing_of_equation hG (equation_generic k)))=_
    rw [point_some]
    exact ActualGaussianWeberStockCoordinateHom318.some_congr hmX hmY
  have hCov := coordinate_gaussian m hG hF jG (V.subtype j) hjG hjF hmj a b (genericPoint k h2)
  have hCov' : E (gaussian hG jG hjG a b (genericPoint k h2))=GF (E (genericPoint k h2)) := hCov
  have hGeneric' : gaussian hG jG hjG a b (genericPoint k h2)=Point.some u v huv := hGeneric
  rw [hGeneric',hE] at hCov'
  have hCalc : E (Point.some u v huv)=Point.some (m u) (m v) (mapped_nonsingular m hF huv) :=
    point_some m hF huv
  have hmapped : GF M=Point.some (m u) (m v) (mapped_nonsingular m hF huv) :=
    hCov'.symm.trans hCalc

  let A := unitX e (X^p)
  let B := unitY e j (Y^p)
  have hxA : m u=V.subtype A := by
    rw [hu,map_unitX,map_pow,hmX]
    change unitX e ((V.subtype X)^p)=V.subtype (unitX e (X^p))
    rw [map_unitX,map_pow]
  have hyB : m v=V.subtype B := by
    have hvg : v=unitY e jG ((yGeneric k)^p) := hv
    rw [hvg,map_unitY,map_pow,hmY,hmj]
    change unitY e (V.subtype j) ((V.subtype Y)^p)=V.subtype (unitY e j (Y^p))
    rw [map_unitY,map_pow]
  let hAB : (curve L).toAffine.Nonsingular (V.subtype A) (V.subtype B) := by
    rw [←hxA,←hyB]
    exact mapped_nonsingular m hF huv
  have hBScalar : GF M=Point.some (V.subtype A) (V.subtype B) hAB :=
    hmapped.trans (ActualGaussianWeberStockCoordinateHom318.some_congr hxA hyB)
  obtain ⟨hFinal,hRead⟩ := red_finite A B hAB

  have hSp : specialize V hR (GF M)=GR (specialize V hR M) := by
    change specializeHom V hF hR (a • M+b • turn hF (V.subtype j) hjF M)=
      a • specializeHom V hF hR M+b • turn hR jR hjR (specializeHom V hF hR M)
    rw [map_add,map_zsmul,map_zsmul]
    have H := specialize_turn V hF hR j hj M
    change specializeHom V hF hR (turn hF (V.subtype j) hjF M)=
      turn hR jR hjR (specializeHom V hF hR M) at H
    rw [H]
  have hScalarRed : red (GF M)=G₀ (red M) := by
    change T (specialize V hR (GF M))=G₀ (T (specialize V hR M))
    rw [hSp]
    exact coordinate_gaussian rho hR h2 jR i hjR hi (hC i) a b _
  have hFixed : red (GF M)=Q₀ := by
    rw [hScalarRed,hRedM]
    exact actual_primary_fixes_probe h2 i hi a b c d ha hb
  have hFinalPoint : Point.some (theta A) (theta B) hFinal=Q₀ :=
    hRead.symm.trans ((congrArg red hBScalar).symm.trans hFixed)

  have hFixY : (1-i)^p=1-i := by
    change frobenius k p (1-i)=_
    rw [map_sub,map_one]
    exact congrArg (1-·) hiFixed
  have hTurnX : theta A=unitX e i := by
    change theta (unitX e (X^p))=_
    rw [map_unitX,map_pow,hθX,hiFixed]
  have hTurnY : theta B=unitY e i (1-i) := by
    change theta (unitY e j (Y^p))=_
    rw [map_unitY,map_pow,hθY,hFixY,show theta j=i from hC i]
  have hBad := no_other_turn_fixes_probe h2 i hi _ _ hFinal hFinalPoint
  cases e with
  | id => rfl
  | minus => exact False.elim (hBad.1 ⟨hTurnX,hTurnY⟩)
  | quarter => exact False.elim (hBad.2 hTurnX)
  | minusQuarter => exact False.elim (hBad.2 hTurnX)

/-- Consumes precisely the four power branches of the same stock
generic point, not a rational function evaluated on a finite set. -/
theorem positive_powers_from_same_named_probe (h2 : (2:k) ≠ 0)
    (i : k) (hi : i^2= -1) (hiFixed : i^p=i)
    (a b c d : ℤ) (ha : a=1-2*(c+d)) (hb : b=2*(c-d))
    (u v : FunctionField k) (huv : (curve (FunctionField k)).toAffine.Nonsingular u v)
    (hGeneric : gaussian (function_two_ne k h2) (constGeneric k i)
      (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi)
      a b (genericPoint k h2)=Point.some u v huv)
    (hShape : (u=(xGeneric k)^p ∧ (v=(yGeneric k)^p ∨ v= -((yGeneric k)^p))) ∨
      (u= -((xGeneric k)^p) ∧
        (v=constGeneric k i*(yGeneric k)^p ∨ v= -(constGeneric k i*(yGeneric k)^p)))) :
    u=(xGeneric k)^p ∧ v=(yGeneric k)^p := by
  have noMinus : ProbeUnit.minus ≠ ProbeUnit.id := by decide
  have noTurn : ProbeUnit.quarter ≠ ProbeUnit.id := by decide
  have noOppositeTurn : ProbeUnit.minusQuarter ≠ ProbeUnit.id := by decide
  rcases hShape with ⟨hx,hy | hy⟩ | ⟨hx,hy | hy⟩
  · exact ⟨hx,hy⟩
  · exact False.elim (noMinus (primary_tag_from_one_affine_probe h2 i hi hiFixed
      a b c d ha hb .minus u v huv hGeneric hx hy))
  · exact False.elim (noTurn (primary_tag_from_one_affine_probe h2 i hi hiFixed
      a b c d ha hb .quarter u v huv hGeneric hx hy))
  · exact False.elim (noOppositeTurn (primary_tag_from_one_affine_probe h2 i hi hiFixed
      a b c d ha hb .minusQuarter u v huv hGeneric hx hy))

end ActualGaussianWeberPrimaryOneAffineProbe318
