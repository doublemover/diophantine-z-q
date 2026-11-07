module
public import ScalarSource318
public section
namespace ScalarPoleValuation318
variable {F:Type*} [Field F]
set_option maxHeartbeats 0

/-- Odd contact depth separates the even and odd summands, including N=0. -/
theorem sum_value (v:AddValuation F (WithTop ℤ)) (r N Q W:F) (R q:ℤ)
    (hr:v r=R) (hq:v Q=q) (hR:Odd R) (hW:W=N^2+r*Q^2) :
    ∃ k:ℤ,v W=k ∧ k≤R+2*q ∧ (k:WithTop ℤ)≤2 • v N := by
  have hqterm:v (r*Q^2)=(R+2*q:ℤ) := by
    rw [v.map_mul,v.map_pow,hr,hq]
    norm_cast
  by_cases hn:N=0
  · refine ⟨R+2*q,?_,le_rfl,?_⟩
    · rw [hW,hn,zero_pow (by decide:2≠0),zero_add]; exact hqterm
    · simp [hn,two_nsmul]
  obtain ⟨n,hnv⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hn)
  have hnterm:v (N^2)=(2*n:ℤ) := by rw [v.map_pow,←hnv]; norm_cast
  have hne:(2*n:ℤ)≠R+2*q := by obtain ⟨j,hj⟩ := hR; omega
  refine ⟨min (2*n) (R+2*q),?_,min_le_right _ _,?_⟩
  · rw [hW,v.map_add_of_distinct_val]
    · rw [hnterm,hqterm]; norm_cast
    · rw [hnterm,hqterm]; exact_mod_cast hne
  · rw [←hnv]
    have hi := min_le_left (2*n) (R+2*q)
    norm_cast

/-- Literal pole obstruction forces the current scalar bounds. No real
positivity, reduction map, or logarithm input is used. -/
theorem pole_bounds (v:AddValuation F (WithTop ℤ))
    (r N Q W b c:F) (R:ℤ) (hr:v r=R) (hRpos:0<R) (hR:Odd R)
    (hc:v c=0) (hQ:Q≠0) (hW:W=N^2+r*Q^2)
    (hb:b*(1+c*r)^2=c*r*W^2)
    (hpole:∀k:ℤ,v b=k→Odd k→0≤k) :
    W≠0 ∧ (-R:WithTop ℤ)<4 • v N ∧
      ∃q:ℤ,v Q=q ∧ -3*R<4*q := by
  obtain ⟨q,hq⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hQ)
  obtain ⟨k,hk,hkq,hkN⟩ := sum_value v r N Q W R q hr hq.symm hR hW
  have hW0:W≠0 := (v.ne_top_iff).mp (by rw [hk]; simp)
  have hcr:v (c*r)=R := by rw [v.map_mul,hc,hr,zero_add]
  have hden:v (1+c*r)=0 := by
    rw [v.map_add_eq_of_lt_left (by rw [v.map_one,hcr]; exact_mod_cast hRpos),v.map_one]
  have hcr0:c*r≠0 := (v.ne_top_iff).mp (by rw [hcr]; simp)
  have hb0:b≠0 := by
    intro hz
    rw [hz,zero_mul] at hb
    exact (mul_ne_zero hcr0 (pow_ne_zero _ hW0)) hb.symm
  obtain ⟨bval,hbval⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hb0)
  have hid:=congrArg v hb
  rw [v.map_mul,v.map_mul,v.map_pow,v.map_pow,hden,hcr,hk,←hbval] at hid
  have hbint:bval=R+2*k := by
    simp only [nsmul_zero,add_zero] at hid
    have hh:bval=R+2 • k := by exact_mod_cast hid
    simpa [nsmul_eq_mul] using hh
  have hbodd:Odd bval := by obtain ⟨j,hj⟩:=hR; exact ⟨j+k,by omega⟩
  have hbnonneg:=hpole bval hbval.symm hbodd
  have hbpos:0<R+2*k := by obtain ⟨j,hj⟩:=hbodd; omega
  have hNbound:((2*k:ℤ):WithTop ℤ)≤4 • v N := by
    have hh := add_le_add hkN hkN
    have he:((2*k:ℤ):WithTop ℤ)=2 • (k:WithTop ℤ) := by norm_cast
    rw [he]
    simpa only [←two_nsmul,←mul_nsmul,show (2*2:ℕ)=4 by rfl] using hh
  refine ⟨hW0,lt_of_lt_of_le ?_ hNbound,q,hq.symm,?_⟩
  · exact_mod_cast (show -R<2*k by omega)
  · omega

open CircuitReplay Raw318FinalReplay
/-- The exact source scalar pole supplies both strict valuation bounds. -/
theorem source_bounds (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (v:AddValuation ℚ (WithTop ℤ)) (R:ℤ)
    (hr:v (ScalarSource318.r w)=R) (hRpos:0<R) (hR:Odd R)
    (hc:v (114444:ℚ)=0) (h3:v (3:ℚ)=0) (h17:v (17:ℚ)=0) :
    ScalarSource318.W w≠0 ∧ (-R:WithTop ℤ)<4 • v (ScalarSource318.N w) ∧
      ∃q:ℤ,v (ScalarSource318.Q w)=q ∧ -3*R<4*q := by
  exact pole_bounds v _ _ _ _ _ _ R hr hRpos hR hc
    (ScalarSource318.Q_nonzero S w source) rfl
    (ScalarSource318.pole_relation S w source)
    (fun k hk hkodd => RawSourcePole318.scalar_no_negative_odd S w source v k hk hkodd h17 h3)

/-- The actual exponent fifteen turns the pole bound into norm order30. -/
theorem source_norm_ratio_bound (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (v:AddValuation ℚ (WithTop ℤ)) (R:ℤ)
    (hr:v (ScalarSource318.r w)=R) (hRpos:0<R) (hR:Odd R)
    (hc:v (114444:ℚ)=0) (h3:v (3:ℚ)=0) (h17:v (17:ℚ)=0) :
    ∃n:ℤ,v (w 308/w 37)=n ∧ 15≤n ∧
      v (AnchorNorm318.norm (ScalarSource318.fR w/CompressedOrientation318.fH w))=(2*n:ℤ) := by
  obtain ⟨hW,hN,q,hq,hqbound⟩ := source_bounds S w source v R hr hRpos hR hc h3 h17
  have hnR := (RawAnchorNorm318.scalar_inverse_norm S w source).2.2
  have hnH := ScalarSource318.normH_nonzero S w source
  have hn0:w 308/w 37≠0 := div_ne_zero hnR hnH
  obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hn0)
  have hQ:ScalarSource318.Q w=(w 308/w 37)/(ScalarSource318.r w)^15 := by
    rw [ScalarSource318.Q_formula S w source,div_div]
  have hval:=congrArg v hQ
  rw [v.map_div,v.map_pow,hr,←hn,hq] at hval
  have he:q=n-15*R := by exact_mod_cast hval
  refine ⟨n,hn.symm,by omega,?_⟩
  rw [ScalarSource318.norm_ratio S w source,v.map_pow,←hn]
  norm_cast

end ScalarPoleValuation318

#print axioms ScalarPoleValuation318.sum_value
#print axioms ScalarPoleValuation318.pole_bounds

#print axioms ScalarPoleValuation318.source_bounds
#print axioms ScalarPoleValuation318.source_norm_ratio_bound
