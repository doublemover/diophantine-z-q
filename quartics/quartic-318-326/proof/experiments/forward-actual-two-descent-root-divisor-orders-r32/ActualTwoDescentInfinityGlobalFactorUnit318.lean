module
public import ActualTwoDescentOriginalNativeRootFunctionIdentity318
public section
noncomputable section
namespace ActualTwoDescentInfinityGlobalFactorUnit318
open ActualTwoDescentInfinityChartRing318
variable {K : Type*} [Field K] [CharZero K]

def chartTail (n : K) : InfinityChart n :=
  -chartCoefficient n (2*n)*chartU n+chartCoefficient n (3*n^2)*chartV n
lemma actual_chart_factor_tail (n : K) : chartFactor n=1+chartU n*chartTail n := by
  unfold chartFactor chartTail
  ring

/-- Explicit Bezout inverse on the ENTIRE original Y=1 chart.
Local invertibility at O alone is not used to assert this global result. -/
def chartFactorInverse (n : K) : InfinityChart n :=
  1-chartU n*chartTail n+(chartU n)^2*(chartTail n)^2-chartV n*(chartTail n)^3
lemma actual_chart_factor_inverse (n : K) : chartFactor n*chartFactorInverse n=1 := by
  have h := actual_chart_cubic_relation n
  rw [actual_chart_factor_tail] at h ⊢
  unfold chartFactorInverse
  linear_combination -(chartTail n)^3*h

def chartFactorUnit (n : K) : (InfinityChart n)ˣ :=
  Units.mkOfMulEqOne (chartFactor n) (chartFactorInverse n) (actual_chart_factor_inverse n)
def globalCubeUnit (n : K) : (InfinityChart n)ˣ := (chartFactorUnit n)⁻¹

/-- v is u³ times an ACTUAL GLOBAL chart unit, not merely a local unit. -/
lemma actual_global_v_unit_cube (n : K) :
    chartV n=(globalCubeUnit n : InfinityChart n)*chartU n^3 := by
  have h := actual_chart_cubic_relation n
  change chartV n*(chartFactorUnit n : InfinityChart n)=chartU n^3 at h
  calc
    chartV n=((((chartFactorUnit n)⁻¹ : (InfinityChart n)ˣ) : InfinityChart n)*
      (chartFactorUnit n : InfinityChart n))*chartV n := by simp
    _=(((chartFactorUnit n)⁻¹ : (InfinityChart n)ˣ) : InfinityChart n)*
      (chartV n*(chartFactorUnit n : InfinityChart n)) := by ring
    _=(globalCubeUnit n : InfinityChart n)*chartU n^3 := by rw [h]; rfl
end ActualTwoDescentInfinityGlobalFactorUnit318
