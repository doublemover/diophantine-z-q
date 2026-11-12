module
public import ActualTwoDescentInfinityNativeFractionFunctions318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace ActualTwoDescentAffineChartCoordinates318
open Polynomial ActualTwoDescentEllipticModel318
variable {K : Type*} [Field K] [CharZero K]

abbrev AffineChart (n : K) := (curve n).toAffine.CoordinateRing
def affineX (n : K) : AffineChart n := AdjoinRoot.of (curve n).toAffine.polynomial X
def affineY (n : K) : AffineChart n := AdjoinRoot.root (curve n).toAffine.polynomial
def affineCoefficient (n : K) : K →+* AffineChart n :=
  (AdjoinRoot.of (curve n).toAffine.polynomial).comp C

lemma actual_affine_cubic (n : K) :
    affineY n^2-affineX n^3-2*affineCoefficient n n*affineX n^2+
      3*(affineCoefficient n n)^2*affineX n=0 := by
  have h := AdjoinRoot.eval₂_root (curve n).toAffine.polynomial
  simp [WeierstrassCurve.Affine.polynomial,curve,affineX,affineY,affineCoefficient] at h ⊢
  linear_combination h

lemma actual_affine_y_nonzero (n : K) : affineY n ≠ 0 := by
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
    (WeierstrassCurve.Affine.monic_polynomial (W:= (curve n).toAffine)) Polynomial.X_ne_zero
    (by rw [Polynomial.natDegree_X,WeierstrassCurve.Affine.natDegree_polynomial]; norm_num)

/-- Polynomial overlap algebra over ANY commutative ring: only the
stated inverse relation is used, not division in a hypothetical field. -/
lemma actual_affine_to_infinity_relation {T : Type*} [CommRing T]
    (n x y z : T) (hc : y^2-x^3-2*n*x^2+3*n^2*x=0) (hi : y*z=1) :
    z-(x*z)^3-2*n*(x*z)^2*z+3*n^2*(x*z)*z^2=0 := by
  linear_combination z^3*hc-z*(y*z+1)*hi

lemma actual_infinity_to_affine_relation {T : Type*} [CommRing T]
    (n u v z : T) (hc : v-u^3-2*n*u^2*v+3*n^2*u*v^2=0) (hi : v*z=1) :
    z^2-(u*z)^3-2*n*(u*z)^2+3*n^2*(u*z)=0 := by
  linear_combination z^3*hc-(z^2*(1-2*n*u^2)+3*n^2*u*z*(v*z+1))*hi

lemma actual_inverse_unique {T : Type*} [CommRing T] (a b c : T)
    (hb : a*b=1) (hc : a*c=1) : b=c := by
  calc
    b=b*(a*c) := by rw [hc,mul_one]
    _=(a*b)*c := by ring
    _=c := by rw [hb,one_mul]
end ActualTwoDescentAffineChartCoordinates318
