module
public import ActualTwoDescentInfinityFieldPoleComparison318
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public section
noncomputable section
namespace ActualTwoDescentInfinitySwappedCubic318
open Polynomial ActualTwoDescentInfinityChartRing318
variable {K : Type*} [Field K] [CharZero K]

/-- Same infinity equation with u as the OUTER variable and v as the
coefficient variable. Its constant term is -v, so Eisenstein is genuine. -/
def swappedPolynomial (n : K) : Polynomial (Polynomial K) :=
  Cubic.toPoly ⟨1,C (2*n)*X,-(C (3*n^2)*X^2),-X⟩

lemma actual_swapped_monic (n : K) : (swappedPolynomial n).Monic :=
  Cubic.monic_of_a_eq_one'
lemma actual_swapped_degree (n : K) : (swappedPolynomial n).degree=3 := by
  simpa only [swappedPolynomial] using
    (Cubic.degree_of_a_ne_zero' (R:=Polynomial K) (b:=C (2*n)*X)
      (c:= -(C (3*n^2)*X^2)) (d:= -X) one_ne_zero)
lemma actual_swapped_natDegree (n : K) : (swappedPolynomial n).natDegree=3 := by
  simpa only [swappedPolynomial] using
    (Cubic.natDegree_of_a_ne_zero' (R:=Polynomial K) (b:=C (2*n)*X)
      (c:= -(C (3*n^2)*X^2)) (d:= -X) one_ne_zero)

abbrev SwappedChart (n : K) := AdjoinRoot (swappedPolynomial n)
def swappedU (n : K) : SwappedChart n := AdjoinRoot.root (swappedPolynomial n)
def swappedV (n : K) : SwappedChart n := AdjoinRoot.of (swappedPolynomial n) X
def swappedCoefficient (n : K) : K →+* SwappedChart n :=
  (AdjoinRoot.of (swappedPolynomial n)).comp C

lemma actual_swapped_relation (n : K) :
    swappedU n^3+swappedCoefficient n (2*n)*swappedV n*swappedU n^2-
      swappedCoefficient n (3*n^2)*swappedV n^2*swappedU n-swappedV n=0 := by
  have h := AdjoinRoot.eval₂_root (swappedPolynomial n)
  simpa [swappedPolynomial,Cubic.toPoly,swappedU,swappedV,swappedCoefficient,
    sub_eq_add_neg,mul_assoc] using h

end ActualTwoDescentInfinitySwappedCubic318
