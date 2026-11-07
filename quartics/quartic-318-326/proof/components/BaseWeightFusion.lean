module
public import QuarticOptimization
public section
namespace BaseWeightFusion
variable {K : Type*} [Field K]

theorem equivalence (e q delta F : K) (hd : delta ≠ 0)
    (he : q*delta^3=e) : e*F=delta^5 ↔ q*F=delta^2 := by
  constructor
  · intro h
    have hz : delta^3*(q*F-delta^2)=0 := by
      rw [←he] at h
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero 3 hd))
  · intro h
    calc
      e*F=(q*delta^3)*F := by rw [he]
      _=(q*F)*delta^3 := by ring
      _=delta^5 := by rw [h]; ring

theorem domains (e q delta F : K) (he : e ≠ 0)
    (hdefinition : q*delta^3=e) (hweight : q*F=delta^2) :
    q ≠ 0 ∧ delta ≠ 0 ∧ F ≠ 0 := by
  have hp : q*delta^3 ≠ 0 := by rwa [hdefinition]
  have hq : q ≠ 0 := (mul_ne_zero_iff.mp hp).1
  have hd3 : delta^3 ≠ 0 := (mul_ne_zero_iff.mp hp).2
  have hd : delta ≠ 0 := by intro h; simp [h] at hd3
  refine ⟨hq,hd,?_⟩
  intro hF
  have hz : delta^2=0 := by simpa [hF] using hweight.symm
  exact (pow_ne_zero 2 hd) hz

end BaseWeightFusion
