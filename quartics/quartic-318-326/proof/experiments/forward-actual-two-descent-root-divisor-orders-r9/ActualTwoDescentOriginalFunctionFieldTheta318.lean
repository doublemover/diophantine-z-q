module
public import ActualTwoDescentOriginalThetaMultipliers318
public section
noncomputable section
namespace ActualTwoDescentOriginalFunctionFieldTheta318
open ActualTwoDescentEllipticModel318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentOriginalRootTranslations318 ActualTwoDescentOriginalThetaMultipliers318
open WeierstrassCurve.Affine.CoordinateRing
variable {K : Type*} [Field K] [CharZero K]

abbrev OriginalFunctionField (n : K) := (curve n).toAffine.FunctionField

def functionCoefficientMap (n : K) : K →+* OriginalFunctionField n :=
  (algebraMap (curve n).toAffine.CoordinateRing (OriginalFunctionField n)).comp
    ((mk (curve n).toAffine).comp
      ((Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)).comp Polynomial.C))

def functionX (n : K) : OriginalFunctionField n :=
  algebraMap (curve n).toAffine.CoordinateRing (OriginalFunctionField n)
    (mk (curve n).toAffine (Polynomial.C Polynomial.X))

/-- A literal original affine root function in the NATIVE function field. -/
def rootFunction (n a : K) : OriginalFunctionField n :=
  algebraMap (curve n).toAffine.CoordinateRing (OriginalFunctionField n)
    (XClass (curve n).toAffine a)

lemma actual_root_function_identity (n a : K) :
    rootFunction n a=functionX n-functionCoefficientMap n a := by
  simp [rootFunction,functionX,functionCoefficientMap,XClass]

lemma actual_root_function_nonzero (n a : K) : rootFunction n a ≠ 0 := by
  intro h
  apply XClass_ne_zero a
  apply IsFractionRing.injective (curve n).toAffine.CoordinateRing (OriginalFunctionField n)
  change rootFunction n a=algebraMap (curve n).toAffine.CoordinateRing (OriginalFunctionField n) 0
  simpa only [map_zero] using h

lemma actual_native_root_weight (n : K) (i : Fin 3) :
    rootWeight (functionCoefficientMap n n) (functionX n) i=rootFunction n (root n i) := by
  rw [actual_root_function_identity]
  fin_cases i <;> simp [rootWeight,root]

/-- Nonvanishing at the generic point is proved in the native coordinate
ring and fraction field, rather than assumed or inferred from rational points. -/
lemma actual_native_away_roots (n : K) :
    AwayRoots (functionCoefficientMap n n) (functionX n) := by
  intro i
  rw [actual_native_root_weight]
  exact actual_root_function_nonzero n _

/-- This is equality in the ORIGINAL elliptic function field. No separate
rational-function field, test-point function space or arbitrary x substitutes. -/
theorem actual_native_theta_commutator (n : K) (hn : n ≠ 0) (i j : Fin 3) :
    thetaCommutator (functionCoefficientMap n n) (functionX n) i j=
      if i=j then (1 : OriginalFunctionField n) else -1 :=
  actual_theta_commutator _ _ (by
    intro h
    apply hn
    apply (functionCoefficientMap n).injective
    simpa only [map_zero] using h) (actual_native_away_roots n) i j

lemma actual_native_theta_square (n : K) :
    thetaMultiplier (functionCoefficientMap n n) (functionX n) 0 0=
      -3*(functionCoefficientMap n n)^2 ∧
    thetaMultiplier (functionCoefficientMap n n) (functionX n) 1 1=
      4*(functionCoefficientMap n n)^2 ∧
    thetaMultiplier (functionCoefficientMap n n) (functionX n) 2 2=
      12*(functionCoefficientMap n n)^2 :=
  actual_theta_square_multipliers _ _ (actual_native_away_roots n)

end ActualTwoDescentOriginalFunctionFieldTheta318
