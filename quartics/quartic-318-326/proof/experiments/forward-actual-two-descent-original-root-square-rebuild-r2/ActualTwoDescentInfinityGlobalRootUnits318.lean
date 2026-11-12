module
public import ActualTwoDescentInfinityGlobalFactorUnit318
public section
noncomputable section
namespace ActualTwoDescentInfinityGlobalRootUnits318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityNativeDomain318
open ActualTwoDescentOriginalRootIdeals318 ActualTwoDescentInfinityGlobalFactorUnit318
variable {K : Type*} [Field K] [CharZero K]

def globalRootFactor (n : K) (i : Fin 3) : InfinityChart n :=
  1-chartCoefficient n (root n i)*(globalCubeUnit n : InfinityChart n)*chartU n^2

lemma actual_global_root_numerator (n : K) (i : Fin 3) :
    chartU n-chartCoefficient n (root n i)*chartV n=chartU n*globalRootFactor n i := by
  rw [actual_global_v_unit_cube]
  unfold globalRootFactor
  ring

lemma actual_chart_three_root_product (n : K) :
    chartU n*(chartU n-chartCoefficient n n*chartV n)*
      (chartU n+3*chartCoefficient n n*chartV n)=chartV n := by
  have h := actual_chart_cubic_relation n
  unfold chartFactor at h
  simp only [map_mul,map_pow,map_ofNat] at h
  linear_combination -h

/-- Product of the two nontrivial root factors is the produced global
cube unit. This genuinely proves their global invertibility, using the
original cubic and nonzero u rather than only residue1 at O. -/
lemma actual_global_root_factor_product (n : K) :
    globalRootFactor n 1*globalRootFactor n 2=(globalCubeUnit n : InfinityChart n) := by
  apply mul_left_cancel₀ (pow_ne_zero 3 (actual_chart_u_nonzero n))
  have h := actual_chart_three_root_product n
  rw [actual_global_v_unit_cube] at h
  simp [globalRootFactor,root]
  linear_combination h

lemma actual_global_root_factor_unit (n : K) (i : Fin 3) : IsUnit (globalRootFactor n i) := by
  have hp : IsUnit (globalRootFactor n 1*globalRootFactor n 2) := by
    rw [actual_global_root_factor_product]
    exact (globalCubeUnit n).isUnit
  fin_cases i
  · simpa [globalRootFactor,root] using (isUnit_one : IsUnit (1 : InfinityChart n))
  · exact isUnit_of_mul_isUnit_left hp
  · exact isUnit_of_mul_isUnit_right hp

/-- The three ACTUAL original roots, and only those three, are covered
by this whole-chart unit statement. Arbitrary-a local units are weaker. -/
def globalRootUnit (n : K) (i : Fin 3) : (InfinityChart n)ˣ :=
  (actual_global_root_factor_unit n i).unit
lemma actual_global_root_unit_value (n : K) (i : Fin 3) :
    (globalRootUnit n i : InfinityChart n)=globalRootFactor n i :=
  (actual_global_root_factor_unit n i).unit_spec
end ActualTwoDescentInfinityGlobalRootUnits318
