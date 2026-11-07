module
public import QuarticOptimization
public section
namespace SixHeight13Weights
variable {K : Type*} [Field K]

/-- Six helpers for orders8 and29. eDelta is an existing source coordinate;
its reuse is essential to this helper count. -/
theorem outputs (e q delta eDelta a b c x y z : K) (he : e ≠ 0)
    (hqd : q*delta^3=e) (hEd : eDelta=e*delta)
    (ha : a=e^2) (hb : b=a^2) (hc : c*delta=b^2)
    (hx : x*eDelta=c^2) (hy : q*y=x^2) (hz : q*z=y^2) :
    x=q*e^14 ∧ y=q*e^28 ∧ z=q*e^56 := by
  have hq : q ≠ 0 := by intro h; simp [h] at hqd; exact he hqd.symm
  have hb' : b=e^4 := by rw [hb,ha]; ring
  have hc' : c*delta=e^8 := by rw [hc,hb']; ring
  have hh : e*delta^3*x=e^16 := by
    calc
      e*delta^3*x=(x*eDelta)*delta^2 := by rw [hEd]; ring
      _=c^2*delta^2 := by rw [hx]
      _=(c*delta)^2 := by ring
      _=e^16 := by rw [hc']; ring
  have hzero : e^2*(x-q*e^14)=0 := by
    linear_combination q*hh-e*x*hqd
  have hxx : x=q*e^14 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 he))
  have hyy : y=q*e^28 := by
    rw [hxx] at hy
    have hh : q*(y-q*e^28)=0 := by linear_combination hy
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hq)
  have hzz : z=q*e^56 := by
    rw [hyy] at hz
    have hh : q*(z-q*e^56)=0 := by linear_combination hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hq)
  exact ⟨hxx,hyy,hzz⟩

theorem reconstruction (e q delta : K) (he : e ≠ 0) (hqd : q*delta^3=e) :
    ∃ a b c x y z : K,
      a=e^2 ∧ b=a^2 ∧ c*delta=b^2 ∧ x*(e*delta)=c^2 ∧
      q*y=x^2 ∧ q*z=y^2 ∧ x=q*e^14 ∧ z=q*e^56 := by
  have hd : delta ≠ 0 := by intro h; simp [h] at hqd; exact he hqd.symm
  refine ⟨e^2,e^4,e^8/delta,q*e^14,q*e^28,q*e^56,rfl,?_,?_,?_,?_,?_,rfl,rfl⟩
  · ring
  · field_simp
  · field_simp
    exact hqd
  · ring
  · ring

end SixHeight13Weights
