module
public import ActualTwoDescentInfinityChartRing318
public section
noncomputable section
namespace ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityChartRing318
variable {K : Type*} [Field K] [CharZero K]

def originIdeal (n : K) : Ideal (InfinityChart n) := RingHom.ker (originEvaluation n)
instance originIdealPrime (n : K) : (originIdeal n).IsPrime := RingHom.ker_isPrime _
instance originIdealMaximal (n : K) : (originIdeal n).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (actual_origin_surjective n)

/-- The native localization of the actual infinity chart AT O. -/
abbrev InfinityLocalRing (n : K) := Localization.AtPrime (originIdeal n)
def localU (n : K) : InfinityLocalRing n := algebraMap _ _ (chartU n)
def localV (n : K) : InfinityLocalRing n := algebraMap _ _ (chartV n)
def localFactor (n : K) : InfinityLocalRing n := algebraMap _ _ (chartFactor n)
def localCoefficient (n : K) : K →+* InfinityLocalRing n :=
  (algebraMap (InfinityChart n) (InfinityLocalRing n)).comp (chartCoefficient n)

lemma actual_local_factor_unit (n : K) : IsUnit (localFactor n) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (InfinityLocalRing n) (originIdeal n) _).mpr
  change originEvaluation n (chartFactor n) ≠ 0
  rw [actual_origin_factor]
  exact one_ne_zero

lemma actual_local_cubic_relation (n : K) : localV n*localFactor n=localU n^3 := by
  have h := congrArg (algebraMap (InfinityChart n) (InfinityLocalRing n))
    (actual_chart_cubic_relation n)
  simpa only [map_mul,map_pow,localV,localU,localFactor] using h

/-- Native local-ring factorization v=e*u^3, with e an ACTUAL unit.
No valuation or ramification order is inserted as a hypothesis. -/
theorem actual_local_v_unit_cube (n : K) :
    ∃ e : (InfinityLocalRing n)ˣ, localV n=(e : InfinityLocalRing n)*localU n^3 := by
  obtain ⟨e,he⟩ := actual_local_factor_unit n
  refine ⟨e⁻¹,?_⟩
  calc
    localV n = (((e⁻¹ : (InfinityLocalRing n)ˣ) : InfinityLocalRing n)*(e : InfinityLocalRing n))*localV n := by simp
    _ = ((e⁻¹ : (InfinityLocalRing n)ˣ) : InfinityLocalRing n)*(localV n*(e : InfinityLocalRing n)) := by ring
    _ = ((e⁻¹ : (InfinityLocalRing n)ˣ) : InfinityLocalRing n)*localU n^3 := by rw [he,actual_local_cubic_relation]

lemma actual_local_u_in_maximal (n : K) : localU n ∈ IsLocalRing.maximalIdeal (InfinityLocalRing n) := by
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff (InfinityLocalRing n) (originIdeal n) _).mpr
  change originEvaluation n (chartU n)=0
  exact actual_origin_u n

end ActualTwoDescentInfinityLocalParameter318
