module
public import EvenDeltaValuation
public import Mathlib.RingTheory.Valuation.Basic
public section
namespace ValuationCurveParity
variable {K : Type*} [Field K]

/-- Negative-u branch for an actual discrete additive valuation. -/
theorem negative_case (v : AddValuation K (WithTop ℤ)) (D u y : K)
    (hD : v D=0) (hc : y^2=1-D*u^4)
    (a b c : ℤ) (ha : v u=a) (hb : v y=b) (hcval : v (y-1)=c)
    (hneg : a<0) : c=2*a := by
  have hu4 : v (D*u^4)=(4*a : ℤ) := by
    simp only [AddValuation.map_mul,AddValuation.map_pow,hD,ha,zero_add]
    norm_num [show (4:ℕ)=1+1+1+1 by decide,add_nsmul]
    norm_cast
  have hlt : v (D*u^4)<v (1:K) := by rw [hu4, v.map_one]; exact_mod_cast (show 4*a<0 by omega)
  have hy2 := congrArg v hc
  rw [v.map_pow,hb,v.map_sub_eq_of_lt_right hlt] at hy2
  rw [hu4] at hy2
  have hab : 2*b=4*a := by exact_mod_cast hy2
  have hylt : v y<v (1:K) := by rw [hb,v.map_one]; exact_mod_cast (show b<0 by omega)
  have hd := v.map_sub_eq_of_lt_left hylt
  rw [hcval,hb] at hd
  have hcb : c=b := by exact_mod_cast hd
  omega

/-- Positive-delta branch; the residue-characteristic restriction is exactly
that two is a valuation unit. -/
theorem positive_case (v : AddValuation K (WithTop ℤ)) (D u y : K)
    (hD : v D=0) (h2 : v (2:K)=0) (hc : y^2=1-D*u^4)
    (a c : ℤ) (ha : v u=a) (hcval : v (y-1)=c) (hpos : 0<c) : c=4*a := by
  have hp : v (y+1)=0 := by
    have he : y+1=(y-1)+2 := by ring
    rw [he]
    have hlt : v (2:K)<v (y-1) := by
      rw [hcval,h2]
      exact_mod_cast hpos
    exact (v.map_add_eq_of_lt_right hlt).trans h2
  have hid : (y-1)*(y+1)=-(D*u^4) := by linear_combination hc
  have hv := congrArg v hid
  simp only [v.map_mul,v.map_neg,v.map_pow,hcval,hp,hD,ha,add_zero,zero_add] at hv
  exact_mod_cast hv

/-- Nonnegative-u branch forces delta integral. -/
theorem integral_case (v : AddValuation K (WithTop ℤ)) (D u y : K)
    (hD : v D=0) (hc : y^2=1-D*u^4)
    (a b c : ℤ) (ha : v u=a) (hb : v y=b) (hcval : v (y-1)=c)
    (hnonnegative : 0≤a) : 0≤c := by
  have hu4 : 0≤v (D*u^4) := by
    simp only [v.map_mul,v.map_pow,hD,ha,zero_add]
    exact nsmul_nonneg (by exact_mod_cast hnonnegative) _
  have hy2 : 0≤v (y^2) := by
    rw [hc]
    exact v.map_le_sub (by simp) hu4
  rw [v.map_pow,hb] at hy2
  have hb0 : 0≤b := by
    have hh : 0≤2*b := by exact_mod_cast hy2
    omega
  have hd : 0≤v (y-1) := v.map_le_sub (by rw [hb]; exact_mod_cast hb0) (by simp)
  rw [hcval] at hd
  exact_mod_cast hd

theorem even_delta_finite_values (v : AddValuation K (WithTop ℤ)) (D u y : K)
    (hD : v D=0) (h2 : v (2:K)=0) (hc : y^2=1-D*u^4)
    (a b c : ℤ) (ha : v u=a) (hb : v y=b) (hcval : v (y-1)=c) :
    Even c ∧ (0<c → c=4*a ∧ 0<a) := by
  apply EvenDeltaValuation.even_and_positive_case a c
  · exact negative_case v D u y hD hc a b c ha hb hcval
  · intro ha0
    have hc0 := integral_case v D u y hD hc a b c ha hb hcval ha0
    by_cases hz : c=0
    · exact Or.inl hz
    · exact Or.inr (positive_case v D u y hD h2 hc a c ha hcval (by omega))

/-- Intrinsic even valuation of every nonzero delta leaf at a discrete place
where D and two are units. This is a theorem about Mathlib valuations, not an
assumed integer case split or an assertion of a global square root. -/
theorem delta_even (v : AddValuation K (WithTop ℤ)) (D u y : K)
    (hD : v D=0) (h2 : v (2:K)=0) (hc : y^2=1-D*u^4)
    (hdelta : y-1 ≠ 0) : ∃ c : ℤ, v (y-1)=c ∧ Even c := by
  by_cases hu : u=0
  · have hy : (y-1)*(y+1)=0 := by
      rw [hu] at hc
      simp only [zero_pow (by decide : 4≠0),mul_zero,sub_zero] at hc
      linear_combination hc
    have hyp : y+1=0 := (mul_eq_zero.mp hy).resolve_left hdelta
    have hd : y-1=-(2:K) := by linear_combination hyp
    refine ⟨0,?_,⟨0,by norm_num⟩⟩
    simpa [hd] using h2
  by_cases hy : y=0
  · refine ⟨0,?_,⟨0,by norm_num⟩⟩
    simp [hy]
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hu)
  obtain ⟨b,hb⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hy)
  obtain ⟨c,hcv⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hdelta)
  exact ⟨c,hcv.symm,(even_delta_finite_values v D u y hD h2 hc a b c
    ha.symm hb.symm hcv.symm).1⟩

end ValuationCurveParity
