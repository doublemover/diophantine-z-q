module
public import SelectedActualLogRatios318
public section
noncomputable section
namespace ActualReciprocalParameters318
open ActualLogIdentification318 ReciprocalDouble318 ValuativeOrbitBounds318
open ConcreteG8Domain ConcretePadic318 CoherentMultipleCharts318 ActualOrientedLogMembership318
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

lemma z_point (D u v : ℚ_[p]) (hv : v≠0) (hc : v^2=1-D*u^4) :
    zParameter p D (point D u v hv hc)= -u/v := by
  by_cases hu : u=0
  · simp [point,hu,zParameter]
  · simp only [point,dif_neg hu,zParameter]
    field_simp [hu,hv]

lemma w_point (D u v : ℚ_[p]) (hv : v≠0) (hc : v^2=1-D*u^4) :
    wParameter p D (point D u v hv hc)=D*u^4 := by
  by_cases hu : u=0
  · simp [point,hu,wParameter]
  · simp only [point,dif_neg hu,wParameter]
    field_simp

lemma mapped_z (rho : ℚ_[p]) (hr : rho^2=2) (n : ℤ) :
    zParameter p (embedding p rho hr ConcreteG8Domain.D) (mappedPoint p rho hr n)=
      embedding p rho hr (-chartU n/chartV n) := by
  rw [mappedPoint,z_point,map_div₀,map_neg]

lemma mapped_w (rho : ℚ_[p]) (hr : rho^2=2) (n : ℤ) :
    wParameter p (embedding p rho hr ConcreteG8Domain.D) (mappedPoint p rho hr n)=
      embedding p rho hr (ConcreteG8Domain.D*(chartU n)^4) := by
  rw [mappedPoint,w_point,map_mul,map_pow]

/-- Exact finite depth, rather than a chosen lower bound, supplies the analytic
series' multiple-of-four hypothesis. The identity branch is separate. -/
lemma argument_depth (D u : ℚ_[p]) (hD : Padic.addValuation D=0) (hu : u≠0) :
    (D*u^4).valuation=4*u.valuation := by
  have hD0 : D≠0 := (Padic.addValuation.ne_top_iff).mp (by rw [hD]; simp)
  have hw0 : D*u^4≠0 := mul_ne_zero hD0 (pow_ne_zero _ hu)
  have he : Padic.addValuation (D*u^4)=((4*u.valuation:ℤ):WithTop ℤ) := by
    rw [Padic.addValuation.map_mul,Padic.addValuation.map_pow,hD,
      Padic.addValuation.apply hu,zero_add]
    norm_cast <;> simp [nsmul_eq_mul]
  rw [Padic.addValuation.apply hw0] at he
  exact_mod_cast he

lemma finite_depth_ge (u : ℚ_[p]) (hu : u≠0) (r : ℤ)
    (hr : Bound Padic.addValuation r u) : r≤u.valuation := by
  rw [Bound,Padic.addValuation.apply hu] at hr
  exact_mod_cast hr

lemma mapped_u_ne (rho : ℚ_[p]) (hr : rho^2=2) (n : ℤ) (hn : n≠0) :
    embedding p rho hr (chartU n)≠0 := by
  intro he
  exact hn ((chartU_zero_iff n).mp
    ((embedding p rho hr).injective (he.trans (map_zero _).symm)))

/-- The actual D is a unit at either selected embedding away from norm49. -/
lemma coefficient_unit (rho : ℚ_[p]) (hr : rho^2=2) (h7 : ¬p∣49) :
    place p rho hr ConcreteG8Domain.D=0 := by
  have he := SelectedCurveUnits318.conjugate_unit p (-rho) (negative_root p rho hr) h7
  have hc := SelectedCurveUnits318.place_conjugate p rho hr 11 6
  have hD : ConcreteG8Domain.D=pair 11 (-6) := by
    ext <;> norm_num [ConcreteG8Domain.D,i,pair,pow_two]
  rw [hD,hc]
  exact he

end ActualReciprocalParameters318
