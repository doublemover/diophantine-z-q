module
public import ActualTwoDescentInfinityProjectiveChart318
public section
noncomputable section
namespace ActualTwoDescentInfinityChartRing318
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- K[u,v] modulo the LITERAL original infinity-chart equation. -/
def infinityPolynomial (n : K) : Polynomial (Polynomial K) :=
  X-C (X^3)-C (C (2*n)*X^2)*X+C (C (3*n^2)*X)*X^2
abbrev InfinityChart (n : K) := AdjoinRoot (infinityPolynomial n)
def chartU (n : K) : InfinityChart n := AdjoinRoot.of (infinityPolynomial n) X
def chartV (n : K) : InfinityChart n := AdjoinRoot.root (infinityPolynomial n)
def chartCoefficient (n : K) : K →+* InfinityChart n :=
  (AdjoinRoot.of (infinityPolynomial n)).comp C

def chartFactor (n : K) : InfinityChart n :=
  1-chartCoefficient n (2*n)*chartU n^2+
    chartCoefficient n (3*n^2)*chartU n*chartV n

lemma actual_chart_cubic_relation (n : K) : chartV n*chartFactor n=chartU n^3 := by
  have h := AdjoinRoot.eval₂_root (infinityPolynomial n)
  simp only [infinityPolynomial,eval₂_add,eval₂_sub,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C,
    map_mul,map_pow] at h
  change chartV n-chartU n^3-chartCoefficient n (2*n)*chartU n^2*chartV n+
    (chartCoefficient n (3*n^2)*chartU n)*chartV n^2=0 at h
  unfold chartFactor
  linear_combination h

/-- The actual evaluation at O, descended through the original equation. -/
def originEvaluation (n : K) : InfinityChart n →+* K :=
  AdjoinRoot.lift (Polynomial.evalRingHom 0) 0 (by simp [infinityPolynomial])

@[simp] lemma actual_origin_u (n : K) : originEvaluation n (chartU n)=0 := by
  simp [originEvaluation,chartU]
@[simp] lemma actual_origin_v (n : K) : originEvaluation n (chartV n)=0 := by
  simp [originEvaluation,chartV]
@[simp] lemma actual_origin_coefficient (n a : K) :
    originEvaluation n (chartCoefficient n a)=a := by
  simp [originEvaluation,chartCoefficient]

lemma actual_origin_surjective (n : K) : Function.Surjective (originEvaluation n) :=
  fun a => ⟨chartCoefficient n a,actual_origin_coefficient n a⟩

@[simp] lemma actual_origin_factor (n : K) : originEvaluation n (chartFactor n)=1 := by
  simp [chartFactor]

end ActualTwoDescentInfinityChartRing318
