module
public import ActualTwoDescentOriginalGlobalTensorSquare318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootEvaluation318
open Polynomial ActualTwoDescentEllipticModel318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentRootCofactorData318
variable {K : Type*} [Field K] [CharZero K]

/-- Evaluation at the literal original affine point (a,0). -/
def rootEvaluation (n : K) (i : Fin 3) : AffineChart n →+* K :=
  AdjoinRoot.lift (Polynomial.evalRingHom (root n i)) 0 (by
    fin_cases i <;> simp [WeierstrassCurve.Affine.polynomial,curve,root] <;> ring)
@[simp] lemma actual_evaluation_x (n : K) (i : Fin 3) :
    rootEvaluation n i (affineX n)=root n i := by simp [rootEvaluation,affineX]
@[simp] lemma actual_evaluation_y (n : K) (i : Fin 3) :
    rootEvaluation n i (affineY n)=0 := by simp [rootEvaluation,affineY]
@[simp] lemma actual_evaluation_coefficient (n a : K) (i : Fin 3) :
    rootEvaluation n i (affineCoefficient n a)=a := by
  simp [rootEvaluation,affineCoefficient]
@[simp] lemma actual_evaluation_numerator (n : K) (i : Fin 3) :
    rootEvaluation n i (rootNumerator n i)=0 := by simp [rootNumerator]
lemma actual_evaluation_surjective (n : K) (i : Fin 3) :
    Function.Surjective (rootEvaluation n i) :=
  fun a => ⟨affineCoefficient n a,actual_evaluation_coefficient n a i⟩
lemma actual_evaluation_cofactor (n : K) (i : Fin 3) :
    rootEvaluation n i (rootCofactor n i)=rootDerivative n i := by
  have h := congrArg (rootEvaluation n i) (actual_root_bezout n i)
  simpa only [map_sub,map_mul,actual_evaluation_numerator,zero_mul,sub_zero,
    actual_evaluation_coefficient] using h
end ActualTwoDescentOriginalRootEvaluation318
