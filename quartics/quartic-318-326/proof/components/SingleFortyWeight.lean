module
public import QuarticOptimization
public section
namespace SingleFortyWeight
variable {K : Type*} [Field K]

theorem single_forty_weight (e q a b c x T V W : K) (he : e ≠ 0)
    (hea : e*a = 1) (hab : a*b = e^2) (hac : a*c = b^2)
    (hxT : x*T = c^2) (hTW : T*W = a^2)
    (hV : V^2 = q*T) (hW : W^2 = x^2*V) :
    x = q*e^78 := by
  have hb : b = e^3 := by
    calc
      b = (e*a)*b := by rw [hea]; simp
      _ = e*(a*b) := by ring
      _ = e*e^2 := by rw [hab]
      _ = e^3 := by ring
  have hc : c = e^7 := by
    calc
      c = (e*a)*c := by rw [hea]; simp
      _ = e*(a*c) := by ring
      _ = e*b^2 := by rw [hac]
      _ = e^7 := by rw [hb]; ring
  have hxT' : x*T = e^14 := by
    calc
      x*T = c^2 := hxT
      _ = e^14 := by rw [hc]; ring
  have hx : x ≠ 0 := by
    intro h
    have hz : e^14 = 0 := by simpa [h] using hxT'.symm
    exact (pow_ne_zero 14 he) hz
  have ha2 : a^2*e^2 = 1 := by
    calc
      a^2*e^2 = (e*a)^2 := by ring
      _ = 1 := by rw [hea]; simp
  have hW' : W*e^16 = x := by
    calc
      W*e^16 = (x*T)*W*e^2 := by rw [hxT']; ring
      _ = x*(T*W)*e^2 := by ring
      _ = x*a^2*e^2 := by rw [hTW]
      _ = x := by rw [mul_assoc, ha2, mul_one]
  have hVsq : W^2*e^32 = x^2 := by
    calc
      W^2*e^32 = (W*e^16)^2 := by ring
      _ = x^2 := by rw [hW']
  rw [hW] at hVsq
  have hz : x^2*(V*e^32-1)=0 := by linear_combination hVsq
  have hV' : V*e^32 = 1 := sub_eq_zero.mp
    ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hx))
  have hqT : q*T*e^64 = 1 := by
    calc
      q*T*e^64 = V^2*e^64 := by rw [hV]
      _ = (V*e^32)^2 := by ring
      _ = 1 := by rw [hV']; simp
  calc
    x = x*(q*T*e^64) := by rw [hqT]; simp
    _ = (x*T)*q*e^64 := by ring
    _ = q*e^78 := by rw [hxT']; ring

theorem single_forty_converse (e q : K) (he : e ≠ 0) (hq : q ≠ 0) :
    let a := 1/e
    let b := e^3
    let c := e^7
    let x := q*e^78
    let T := 1/(q*e^64)
    let V := 1/e^32
    let W := q*e^62
    e*a=1 ∧ a*b=e^2 ∧ a*c=b^2 ∧ x*T=c^2 ∧ T*W=a^2 ∧
      V^2=q*T ∧ W^2=x^2*V := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp [he,hq] <;> ring

end SingleFortyWeight
