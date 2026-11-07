module
public import ValuationEvenNormChain
public section

/-! Soundness of the literal 318 four-witness pole rows. No restricted-converse,
rank, nonzero-witness, or pole theorem assumption is used. -/
namespace SourcePole318
variable {K : Type*} [Field K]

theorem square_not_odd (v : AddValuation K (WithTop ℤ)) (x : K)
    (a : ℤ) (ha : v (x^2)=a) (ho : Odd a) : False := by
  have hx : x≠0 := by intro hz; simp [hz] at ha
  obtain ⟨b,hb⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hx)
  rw [v.map_pow,←hb] at ha
  have hi : 2*b=a := by exact_mod_cast ha
  obtain ⟨j,hj⟩ := ho
  omega

theorem pair_value (v : AddValuation K (WithTop ℤ)) (x y : K)
    (a b : ℤ) (hx : v x=a) (hy : v y=b) (h3 : v (3:K)=0) (hne : a≠b) :
    v ((x-y)*(x+3*y))=(2*min a b : ℤ) := by
  have hsub : v (x-y)=(min a b : ℤ) := by
    rw [sub_eq_add_neg,v.map_add_of_distinct_val]
    · rw [v.map_neg,hx,hy]
      norm_cast
    · rw [v.map_neg,hx,hy]
      exact_mod_cast hne
  have hadd : v (x+3*y)=(min a b : ℤ) := by
    rw [v.map_add_of_distinct_val]
    · rw [v.map_mul,h3,hx,hy,zero_add]
      norm_cast
    · rw [v.map_mul,h3,hx,hy,zero_add]
      exact_mod_cast hne
  rw [v.map_mul,hsub,hadd]
  norm_cast
  ring

/-- Zero ordinates of the first conic are allowed. -/
theorem first_forces_unit (v : AddValuation K (WithTop ℤ))
    (b e P : K) (k : ℤ) (hb : v b=k) (hk : Odd k)
    (h17 : v (17:K)=0) (h3 : v (3:K)=0)
    (hfirst : 17*P^2=b*((17-e)*(17+3*e))) : v e=0 := by
  by_cases he : e=0
  · have hid := congrArg v hfirst
    simp only [he,sub_zero,mul_zero,add_zero,v.map_mul,h17,zero_add,add_zero,hb] at hid
    exact (square_not_odd v P k hid hk).elim
  obtain ⟨j,hj⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr he)
  by_cases hj0 : j=0
  · simpa [hj0] using hj.symm
  have hvprod := pair_value v 17 e 0 j h17 hj.symm h3 (Ne.symm hj0)
  have hid := congrArg v hfirst
  rw [v.map_mul,v.map_mul,h17,hb,hvprod,zero_add] at hid
  have hvP : v (P^2)=(k+2*min 0 j : ℤ) := by exact_mod_cast hid
  have hodd : Odd (k+2*min 0 j) := by
    obtain ⟨r,hr⟩ := hk
    exact ⟨r+min 0 j,by omega⟩
  exact (square_not_odd v P _ hvP hodd).elim

/-- The exact two factored source pole equations rule out negative odd
valuation of b. Only 3 and 17 must be valuation units for this module. -/
theorem no_negative_odd (v : AddValuation K (WithTop ℤ))
    (b e P s q : K) (k : ℤ) (hb : v b=k) (hk : Odd k)
    (h17 : v (17:K)=0) (h3 : v (3:K)=0)
    (hfirst : 17*P^2=b*((17-e)*(17+3*e)))
    (hsecond : 17*q^2=b*((s^2-e*(17-b))*(s^2+3*(e*(17-b))))) : 0≤k := by
  by_contra hn
  have hkneg : k<0 := by omega
  have he := first_forces_unit v b e P k hb hk h17 h3 hfirst
  have hvdiff : v ((17:K)-b)=k := by
    have hlt : v b<v (17:K) := by rw [hb,h17]; exact_mod_cast hkneg
    exact (v.map_sub_eq_of_lt_right hlt).trans hb
  have hvH : v (e*(17-b))=k := by rw [v.map_mul,he,hvdiff,zero_add]
  by_cases hs : s=0
  · have hval : v ((s^2-e*(17-b))*(s^2+3*(e*(17-b))))=(2*k : ℤ) := by
      simp only [hs,zero_pow (by decide : 2≠0),zero_sub,zero_add,v.map_mul,v.map_neg,h3,he,hvdiff,zero_add]
      norm_cast
      ring
    have hid := congrArg v hsecond
    rw [v.map_mul,v.map_mul,h17,hb,hval,zero_add] at hid
    have hvq0 : v (q^2)=(k+2*k : ℤ) := by exact_mod_cast hid
    have hvq : v (q^2)=(3*k : ℤ) := by simpa only [show k+2*k=3*k by ring] using hvq0
    have hodd : Odd (3*k) := by
      obtain ⟨r,hr⟩ := hk
      exact ⟨3*r+1,by omega⟩
    exact square_not_odd v q _ hvq hodd
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hs)
  have hvs : v (s^2)=(2*a : ℤ) := by rw [v.map_pow,←ha]; norm_cast
  have hne : 2*a≠k := by obtain ⟨r,hr⟩ := hk; omega
  have hval := pair_value v (s^2) (e*(17-b)) (2*a) k hvs hvH h3 hne
  have hid := congrArg v hsecond
  rw [v.map_mul,v.map_mul,h17,hb,hval,zero_add] at hid
  have hvq : v (q^2)=(k+2*min (2*a) k : ℤ) := by exact_mod_cast hid
  have hodd : Odd (k+2*min (2*a) k) := by
    obtain ⟨r,hr⟩ := hk
    exact ⟨r+min (2*a) k,by omega⟩
  exact square_not_odd v q _ hvq hodd

/-- Decode the first factored conic from the exact current quadratic rows. -/
theorem first_from_source (b e P H : K) (hH : H=e*(17-b))
    (hrow : 17*P^2-289*b-578*e+34*H+51*e^2-3*e*H=0) :
    17*P^2=b*((17-e)*(17+3*e)) := by
  rw [hH] at hrow
  linear_combination hrow

/-- Decode both factored pole rows, including their two auxiliary gates. -/
theorem source_no_negative_odd (v : AddValuation K (WithTop ℤ))
    (b e P s q H ss T : K) (k : ℤ) (hb : v b=k) (hk : Odd k)
    (h17 : v (17:K)=0) (h3 : v (3:K)=0)
    (hH : H=e*(17-b)) (hss : ss=s^2) (hT : T=(ss-H)*(ss+3*H))
    (hfirst : 17*P^2-289*b-578*e+34*H+51*e^2-3*e*H=0)
    (hsecond : 17*q^2-b*T=0) : 0≤k := by
  apply no_negative_odd v b e P s q k hb hk h17 h3
    (first_from_source b e P H hH hfirst)
  rw [hT,hss,hH] at hsecond
  exact sub_eq_zero.mp hsecond

end SourcePole318
