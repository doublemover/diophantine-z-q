module
public import ActualTwoDescentEllipticModel318
public section
noncomputable section
namespace ActualTwoDescentOriginalFunctionFieldTheta318
open ActualTwoDescentEllipticModel318
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

end ActualTwoDescentOriginalFunctionFieldTheta318
