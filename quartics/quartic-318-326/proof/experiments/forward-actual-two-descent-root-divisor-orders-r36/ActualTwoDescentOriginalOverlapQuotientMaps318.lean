module
public import ActualTwoDescentOriginalPuncturedCharts318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapQuotientMaps318
open Polynomial ActualTwoDescentEllipticModel318 ActualTwoDescentAffineChartCoordinates318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentOriginalPuncturedCharts318
variable {K : Type*} [Field K] [CharZero K]

/-- Actual x=u/v,y=1/v map out of the ORIGINAL affine quotient. -/
def affineToInfinity (n : K) : AffineChart n →+* InfinityPuncture n :=
  AdjoinRoot.lift
    (Polynomial.eval₂RingHom (infinityOpenCoefficient n) (openU n*inverseV n))
    (inverseV n) (by
      have h := actual_infinity_to_affine_relation (infinityOpenCoefficient n n)
        (openU n) (openV n) (inverseV n) (actual_open_infinity_cubic n)
        (actual_open_v_inverse n)
      simp [WeierstrassCurve.Affine.polynomial,curve]
      linear_combination h)

/-- Actual u=x/y,v=1/y map out of the ORIGINAL infinity quotient. -/
def infinityToAffine (n : K) : InfinityChart n →+* AffinePuncture n :=
  AdjoinRoot.lift
    (Polynomial.eval₂RingHom (affineOpenCoefficient n) (openX n*inverseY n))
    (inverseY n) (by
      have h := actual_affine_to_infinity_relation (affineOpenCoefficient n n)
        (openX n) (openY n) (inverseY n) (actual_open_affine_cubic n)
        (actual_open_y_inverse n)
      simp [infinityPolynomial]
      linear_combination h)

@[simp] lemma actual_affine_to_infinity_x (n : K) :
    affineToInfinity n (affineX n)=openU n*inverseV n := by
  simp [affineToInfinity,affineX]
@[simp] lemma actual_affine_to_infinity_y (n : K) :
    affineToInfinity n (affineY n)=inverseV n := by
  simp [affineToInfinity,affineY]
@[simp] lemma actual_affine_to_infinity_coefficient (n a : K) :
    affineToInfinity n (affineCoefficient n a)=infinityOpenCoefficient n a := by
  simp [affineToInfinity,affineCoefficient]
@[simp] lemma actual_infinity_to_affine_u (n : K) :
    infinityToAffine n (chartU n)=openX n*inverseY n := by
  simp [infinityToAffine,chartU]
@[simp] lemma actual_infinity_to_affine_v (n : K) :
    infinityToAffine n (chartV n)=inverseY n := by
  simp [infinityToAffine,chartV]
@[simp] lemma actual_infinity_to_affine_coefficient (n a : K) :
    infinityToAffine n (chartCoefficient n a)=affineOpenCoefficient n a := by
  simp [infinityToAffine,chartCoefficient]
end ActualTwoDescentOriginalOverlapQuotientMaps318
