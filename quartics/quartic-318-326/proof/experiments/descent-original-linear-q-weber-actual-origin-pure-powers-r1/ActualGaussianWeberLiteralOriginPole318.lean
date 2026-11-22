module
public import ActualGaussianWeberValuedPolynomialPole318
public import ActualGaussianWeberPowerSeriesArc318
public import ActualGaussianWeberScalarOnArc318
public import ActualGaussianWeberStockReductionAdd318
public section
noncomputable section

namespace ActualGaussianWeberLiteralOriginPole318

open IsLocalRing Polynomial WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberValuedPolynomialPole318 ActualGaussianWeberPowerSeriesArc318
open ActualGaussianWeberScalarOnArc318 ActualGaussianWeberStockReductionAdd318
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberGaussianScalarSpecialization318
open ActualGaussianWeberQuadraticGenericChart318 ActualGaussianWeberGaussLocalization318
open ActualGaussianWeberTranslationFunctionField318 ActualGaussianWeberOddNormGeneric318

variable {k : Type*} [Field k] [DecidableEq (FunctionField k)]

/-- The actual stock scalar reducing its original Laurent origin arc
to O forces a pole of the same rational generic abscissa. There is
no residue derivative, degree cap, stationarity, or primary-unit input. -/
theorem actual_origin_is_a_pole (h2 : (2:k)≠0) (i : k) (hi : i^2= -1)
    (a b : ℤ) (A B : k[X]) (hB : B≠0)
    (u v : FunctionField k) (hn : (curve (FunctionField k)).toAffine.Nonsingular u v)
    (hGen : gaussian (function_two_ne k h2) (constGeneric k i)
      (by simpa only [map_pow,map_neg,map_one] using congrArg (constGeneric k) hi)
      a b (genericPoint k h2)=Point.some u v hn)
    (hRat : u=fractionMap k (AdjoinRoot.of (relation k) A) /
                 fractionMap k (AdjoinRoot.of (relation k) B)) :
    B.natDegree < A.natDegree := by
  classical
  let V := FormalValuation k
  let hF := formal_two_ne k h2
  let hR := formal_residue_two_ne k h2
  let I := constVal k i
  let hI : I^2= -1 := by
    simpa only [map_pow,map_neg,map_one] using congrArg (constVal k) hi
  let hIF := chosen_square_generic V I hI
  let G := gaussian hF (V.subtype I) hIF a b
  obtain ⟨x,y,hP,hO,_⟩ := formal_origin_arc k h2
  have hx : x∉V := (specialize_some_eq_zero V hR hP).mp hO
  have hiEval : Function.Injective (eval₂RingHom (constField k) x) :=
    evaluation_at_pole_injective V (constVal k) hx
  let P := Point.some x y hP
  let r := A.eval₂ (constField k) x/B.eval₂ (constField k) x
  obtain ⟨w,hw,hActual⟩ := scalar_rational_x_on_arc (constField k) h2 hF i hi a b A B
    x y ((literal_equation x y).mp hP.1) hiEval u v hn hGen hRat
  have hG : G P=Point.some r w hw := hActual
  have hTurn : specialize V hR (turn hF (V.subtype I) hIF P)=0 := by
    have h := specialize_turn V hF hR I hI P
    change specialize V hR (turn hF (V.subtype I) hIF P) =
      turn hR (residue V I) (chosen_square_residue V I hI) (specialize V hR P) at h
    have hZero : specialize V hR P=Point.zero := hO
    rw [hZero] at h
    exact h.trans rfl
  have hGO : specialize V hR (G P)=Point.zero := by
    change specializeHom V hF hR (a • P+b • turn hF (V.subtype I) hIF P)=0
    rw [map_add,map_zsmul,map_zsmul]
    change a • specialize V hR P + b • specialize V hR (turn hF (V.subtype I) hIF P)=0
    have hZero : specialize V hR P=0 := hO
    simp only [hZero,hTurn,zsmul_zero,zero_add]
  rw [hG] at hGO
  have hr : r∉V := (specialize_some_eq_zero V hR hw).mp hGO
  exact lt_of_not_ge (fun hdeg => hr (degree_le_at_pole_integral V (constVal k) hx A B hB hdeg))

end ActualGaussianWeberLiteralOriginPole318
