module
public import ActualTwoDescentOriginalRootInfinityIdealOverlap318
public section
noncomputable section
namespace ActualTwoDescentRootCofactorData318
open ActualTwoDescentEllipticModel318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentAffineChartCoordinates318
open WeierstrassCurve.Affine.CoordinateRing
variable {K : Type*} [Field K] [CharZero K]

def rootNumerator (n : K) (i : Fin 3) : AffineChart n :=
  affineX n-affineCoefficient n (root n i)
def rootCofactor (n : K) : Fin 3 → AffineChart n :=
  ![rootNumerator n 1*rootNumerator n 2,
    rootNumerator n 0*rootNumerator n 2,rootNumerator n 0*rootNumerator n 1]
def rootSlope (n : K) : Fin 3 → K := ![2*n,3*n,-n]
def rootDerivative (n : K) : Fin 3 → K := ![-3*n^2,4*n^2,12*n^2]
def bezoutLinear (n : K) (i : Fin 3) : AffineChart n :=
  affineX n+affineCoefficient n (root n i+rootSlope n i)

lemma actual_root_numerator_class (n : K) (i : Fin 3) :
    XClass (curve n).toAffine (root n i)=rootNumerator n i := by
  change (AdjoinRoot.of (curve n).toAffine.polynomial)
    (Polynomial.X-Polynomial.C (root n i))=_
  rw [map_sub]
  rfl
lemma actual_root_numerator_nonzero (n : K) (i : Fin 3) : rootNumerator n i≠0 := by
  rw [←actual_root_numerator_class]
  exact XClass_ne_zero _
lemma actual_root_cofactor_nonzero (n : K) (i : Fin 3) : rootCofactor n i≠0 := by
  fin_cases i <;> exact mul_ne_zero (actual_root_numerator_nonzero _ _) (actual_root_numerator_nonzero _ _)

lemma actual_root_factorization (n : K) (i : Fin 3) :
    affineY n^2=rootNumerator n i*rootCofactor n i := by
  have h := actual_affine_cubic n
  fin_cases i <;>
    simp [rootNumerator,rootCofactor,root,map_neg,map_mul,map_ofNat] at h ⊢ <;>
    linear_combination h

/-- Explicit Bezout identity for the SAME root and its complementary
quadratic. The constant is the actual cubic derivative at that root. -/
lemma actual_root_bezout (n : K) (i : Fin 3) :
    rootCofactor n i-rootNumerator n i*bezoutLinear n i=
      affineCoefficient n (rootDerivative n i) := by
  fin_cases i <;>
    simp [rootCofactor,rootNumerator,bezoutLinear,root,rootSlope,rootDerivative,
      map_add,map_neg,map_mul,map_pow,map_ofNat] <;> ring
lemma actual_root_derivative_nonzero (n : K) (hn : n≠0) (i : Fin 3) :
    rootDerivative n i≠0 := by
  fin_cases i <;> simp [rootDerivative,hn]
lemma actual_root_ideal_generators (n : K) (i : Fin 3) :
    rootIdeal n i=Ideal.span {rootNumerator n i,affineY n} := by
  change Ideal.span {XClass (curve n).toAffine (root n i),YClass (curve n).toAffine 0}=_
  rw [actual_root_numerator_class]
  congr 1
  simp only [YClass,Polynomial.C_0,sub_zero]
  rfl
end ActualTwoDescentRootCofactorData318
