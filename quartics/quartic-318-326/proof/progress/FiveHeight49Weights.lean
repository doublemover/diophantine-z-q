module
public import QuarticOptimization
public section
namespace FiveHeight49Weights
variable {K : Type*} [Field K]

/-- The nondegenerate five-helper order4/order13 construction. The separate
zero-parameter branch is not assumed away by the source. -/
theorem outputs (e q delta eDelta a c x y z : K) (he : e ≠ 0)
    (hqd : q*delta^3=e) (hEd : eDelta=e*delta)
    (ha : a=e^2) (hc : c*delta=a^2)
    (hx : x*eDelta=c^2) (hy : q*y=x^2) (hz : q*z=y^2) :
    x=q*e^6 ∧ y=q*e^12 ∧ z=q*e^24 := by
  have hq : q ≠ 0 := by intro h; simp [h] at hqd; exact he hqd.symm
  have hc' : c*delta=e^4 := by rw [hc,ha]; ring
  have hh : e*delta^3*x=e^8 := by
    calc
      e*delta^3*x=(x*eDelta)*delta^2 := by rw [hEd]; ring
      _=c^2*delta^2 := by rw [hx]
      _=(c*delta)^2 := by ring
      _=e^8 := by rw [hc']; ring
  have hzero : e^2*(x-q*e^6)=0 := by
    linear_combination q*hh-e*x*hqd
  have hxx : x=q*e^6 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 he))
  have hyy : y=q*e^12 := by
    rw [hxx] at hy
    have hh : q*(y-q*e^12)=0 := by linear_combination hy
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hq)
  have hzz : z=q*e^24 := by
    rw [hyy] at hz
    have hh : q*(z-q*e^24)=0 := by linear_combination hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hq)
  exact ⟨hxx,hyy,hzz⟩

theorem reconstruction (e q delta : K) (he : e ≠ 0) (hqd : q*delta^3=e) :
    ∃ a c x y z : K,
      a=e^2 ∧ c*delta=a^2 ∧ x*(e*delta)=c^2 ∧
      q*y=x^2 ∧ q*z=y^2 ∧ x=q*e^6 ∧ z=q*e^24 := by
  have hd : delta ≠ 0 := by intro h; simp [h] at hqd; exact he hqd.symm
  refine ⟨e^2,e^4/delta,q*e^6,q*e^12,q*e^24,rfl,?_,?_,?_,?_,rfl,rfl⟩
  · field_simp
  · field_simp
    exact hqd
  · ring
  · ring
end FiveHeight49Weights
