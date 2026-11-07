module
public import GlobalSaturationHeight318
public section
namespace DuplicationHeightLocal318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem finite_of_le (z:WithTop ℤ) (n:ℤ) (h:z≤n) : ∃m:ℤ,z=m := by
  have hz:z≠⊤ := by intro he; rw [he] at h; simpa using h
  obtain ⟨m,hm⟩ := WithTop.ne_top_iff_exists.mp hz
  exact ⟨m,hm.symm⟩

/-- Primitive local duplication gcd bound at every place where D is a
unit. With v(2)=e this is 3e, giving zero at good places and six at sqrt2. -/
theorem unit_D_gcd_bound {F:Type*} [Field F] (v:AddValuation F (WithTop ℤ))
    (a b D:F) (A B e:ℤ) (ha:v a=A) (hb:v b=B) (hD:v D=0)
    (h2:v (2:F)=e) (hA:0≤A) (hB:0≤B) (he:0≤e) (hp:min A B=0) :
    min (v ((a^2+D*b^2)^2)) (v (4*a*b*(a^2-D*b^2)))≤(3*e:ℤ) := by
  have ha2:v (a^2)=(2*A:ℤ) := by rw [v.map_pow,ha]; norm_cast
  have hb2:v (D*b^2)=(2*B:ℤ) := by rw [v.map_mul,v.map_pow,hD,hb,zero_add]; norm_cast
  have h4:v (4:F)=(2*e:ℤ) := by
    rw [show (4:F)=2*2 by ring,v.map_mul,h2]
    norm_cast; omega
  by_cases hs:v (a^2+D*b^2)≤(e:ℤ)
  · obtain ⟨s,hsv⟩ := finite_of_le _ e hs
    have hse:s≤e := by rw [hsv] at hs; exact_mod_cast hs
    have hF:v ((a^2+D*b^2)^2)=(2*s:ℤ) := by rw [v.map_pow,hsv]; norm_cast
    apply (min_le_left _ _).trans
    rw [hF]
    exact_mod_cast (show 2*s≤3*e by omega)
  · have hs' : (e:WithTop ℤ)<v (a^2+D*b^2) := lt_of_not_ge hs
    have hAB:A=B := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hab|hba
      · have hz:A=0 := by simpa [min_eq_left hab.le] using hp
        have hsum:v (a^2+D*b^2)=0 := by
          rw [v.map_add_eq_of_lt_left]
          · simpa [hz] using ha2
          · rw [ha2,hb2]; exact_mod_cast (show 2*A<2*B by omega)
        rw [hsum] at hs'
        have : (e:WithTop ℤ)≥0 := by exact_mod_cast he
        exact (not_lt_of_ge this) hs'
      · have hz:B=0 := by simpa [min_eq_right hba.le] using hp
        have hsum:v (a^2+D*b^2)=0 := by
          rw [v.map_add_eq_of_lt_right]
          · simpa [hz] using hb2
          · rw [ha2,hb2]; exact_mod_cast (show 2*B<2*A by omega)
        rw [hsum] at hs'
        have : (e:WithTop ℤ)≥0 := by exact_mod_cast he
        exact (not_lt_of_ge this) hs'
    have hAz:A=0 := by simpa [hAB] using hp
    have hBz:B=0 := by omega
    have hdiff:(a^2+D*b^2)-(a^2-D*b^2)=2*D*b^2 := by ring
    have hdiffval:v ((a^2+D*b^2)-(a^2-D*b^2))=(e:ℤ) := by
      rw [hdiff,v.map_mul,v.map_mul,v.map_pow,h2,hD,hb,hBz]
      simp
    have hmin := v.map_sub (a^2+D*b^2) (a^2-D*b^2)
    rw [hdiffval] at hmin
    have ht:v (a^2-D*b^2)≤(e:ℤ) := (min_le_iff.mp hmin).resolve_left hs
    obtain ⟨t,htv⟩ := finite_of_le _ e ht
    have hte:t≤e := by rw [htv] at ht; exact_mod_cast ht
    have hG:v (4*a*b*(a^2-D*b^2))=(2*e+t:ℤ) := by
      rw [v.map_mul,v.map_mul,v.map_mul,h4,ha,hb,htv,hAz,hBz]
      norm_cast; omega
    apply (min_le_right _ _).trans
    rw [hG]
    exact_mod_cast (show 2*e+t≤3*e by omega)

/-- Primitive local duplication gcd bound at a simple prime divisor of
sqrt(D). The bound four needs no unchecked residue-square assertion. -/
theorem delta_gcd_bound {F:Type*} [Field F] (v:AddValuation F (WithTop ℤ))
    (a b D:F) (A B:ℤ) (ha:v a=A) (hb:v b=B) (hD:v D=(2:ℤ))
    (h2:v (2:F)=0) (hA:0≤A) (hB:0≤B) (hp:min A B=0) :
    min (v ((a^2+D*b^2)^2)) (v (4*a*b*(a^2-D*b^2)))≤(4:ℤ) := by
  have ha2:v (a^2)=(2*A:ℤ) := by rw [v.map_pow,ha]; norm_cast
  have hb2:v (D*b^2)=(2+2*B:ℤ) := by rw [v.map_mul,v.map_pow,hD,hb]; norm_cast
  have h4:v (4:F)=0 := by rw [show (4:F)=2*2 by ring,v.map_mul,h2,zero_add]
  by_cases hs:v (a^2+D*b^2)≤(2:ℤ)
  · obtain ⟨s,hsv⟩ := finite_of_le _ 2 hs
    have hse:s≤2 := by rw [hsv] at hs; exact_mod_cast hs
    have hF:v ((a^2+D*b^2)^2)=(2*s:ℤ) := by rw [v.map_pow,hsv]; norm_cast
    apply (min_le_left _ _).trans
    rw [hF]
    exact_mod_cast (show 2*s≤4 by omega)
  · have hs' : (2:WithTop ℤ)<v (a^2+D*b^2) := lt_of_not_ge hs
    have hBz:B=0 := by
      by_contra hn
      have hAz:A=0 := by omega
      have hsum:v (a^2+D*b^2)=0 := by
        rw [v.map_add_eq_of_lt_left]
        · simpa [hAz] using ha2
        · rw [ha2,hb2,hAz]; exact_mod_cast (show 0<2+2*B by omega)
      rw [hsum] at hs'
      have hh : (2:ℤ)<0 := by exact_mod_cast hs'
      omega
    have hb2' : v (D*b^2)=(2:ℤ) := by simpa [hBz] using hb2
    have haa : v (a^2)=(2:ℤ) := by
      have hh : v ((a^2+D*b^2)-D*b^2)=(2:ℤ) := by
        rw [v.map_sub_eq_of_lt_right]
        · exact hb2'
        · rw [hb2']; exact hs'
      simpa only [add_sub_cancel_right] using hh
    have hAz:A=1 := by rw [ha2] at haa; norm_cast at haa; omega
    have htwo:v (2*D*b^2)=(2:ℤ) := by
      rw [v.map_mul,v.map_mul,v.map_pow,h2,hD,hb,hBz]
      norm_num
    have ht:v (a^2-D*b^2)=(2:ℤ) := by
      have hh : v ((a^2+D*b^2)-2*D*b^2)=(2:ℤ) := by
        rw [v.map_sub_eq_of_lt_right]
        · exact htwo
        · rw [htwo]; exact hs'
      convert hh using 1 <;> congr 1 <;> ring
    have hG:v (4*a*b*(a^2-D*b^2))=(3:ℤ) := by
      rw [v.map_mul,v.map_mul,v.map_mul,h4,ha,hb,ht,hAz,hBz]
      norm_num
    apply (min_le_right _ _).trans
    rw [hG]; exact_mod_cast (show (3:ℤ)≤4 by omega)

/-- Zero projective coordinates are included in the primitive bound. -/
theorem primitive_unit_D_bound {F:Type*} [Field F] (v:AddValuation F (WithTop ℤ))
    (a b D:F) (e:ℤ) (hD:v D=0) (h2:v (2:F)=e) (he:0≤e)
    (hp:min (v a) (v b)=0) :
    min (v ((a^2+D*b^2)^2)) (v (4*a*b*(a^2-D*b^2)))≤(3*e:ℤ) := by
  by_cases haz:a=0
  · have hbz:v b=0 := by simpa [haz] using hp
    have hF:v ((a^2+D*b^2)^2)=0 := by
      simp [haz,v.map_pow,v.map_mul,hD,hbz]
    apply (min_le_left _ _).trans
    rw [hF]; exact_mod_cast (show 0≤3*e by omega)
  by_cases hbz:b=0
  · have haz':v a=0 := by simpa [hbz] using hp
    have hF:v ((a^2+D*b^2)^2)=0 := by simp [hbz,v.map_pow,haz']
    apply (min_le_left _ _).trans
    rw [hF]; exact_mod_cast (show 0≤3*e by omega)
  obtain ⟨A,ha⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr haz)
  obtain ⟨B,hb⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hbz)
  have hp' : min A B=0 := by rw [←ha,←hb] at hp; exact_mod_cast hp
  exact unit_D_gcd_bound v a b D A B e ha.symm hb.symm hD h2 (by omega) (by omega) he hp'

/-- The delta bound also includes both projective coordinate boundaries. -/
theorem primitive_delta_bound {F:Type*} [Field F] (v:AddValuation F (WithTop ℤ))
    (a b D:F) (hD:v D=(2:ℤ)) (h2:v (2:F)=0) (hp:min (v a) (v b)=0) :
    min (v ((a^2+D*b^2)^2)) (v (4*a*b*(a^2-D*b^2)))≤(4:ℤ) := by
  by_cases haz:a=0
  · have hbz:v b=0 := by simpa [haz] using hp
    have hF:v ((a^2+D*b^2)^2)=(4:ℤ) := by
      simp [haz,v.map_pow,v.map_mul,hD,hbz]
      norm_cast
    exact hF ▸ min_le_left _ _
  by_cases hbz:b=0
  · have haz':v a=0 := by simpa [hbz] using hp
    have hF:v ((a^2+D*b^2)^2)=0 := by simp [hbz,v.map_pow,haz']
    apply (min_le_left _ _).trans
    rw [hF]; norm_num
  obtain ⟨A,ha⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr haz)
  obtain ⟨B,hb⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hbz)
  have hp' : min A B=0 := by rw [←ha,←hb] at hp; exact_mod_cast hp
  exact delta_gcd_bound v a b D A B ha.symm hb.symm hD h2 (by omega) (by omega) hp'

/-- Universal primitive duplication gcd bound. This avoids any global
classification of exceptional primes: the loss is bounded by 3v(2)+2v(D).
For D=(3-sqrt2)^2 its global absolute norm contributes exactly392. -/
theorem universal_gcd_bound {F:Type*} [Field F] (v:AddValuation F (WithTop ℤ))
    (a b D:F) (A B d e:ℤ) (ha:v a=A) (hb:v b=B) (hD:v D=d)
    (h2:v (2:F)=e) (hA:0≤A) (hB:0≤B) (hd:0≤d) (he:0≤e) (hp:min A B=0) :
    min (v ((a^2+D*b^2)^2)) (v (4*a*b*(a^2-D*b^2)))≤(3*e+2*d:ℤ) := by
  have ha2:v (a^2)=(2*A:ℤ) := by rw [v.map_pow,ha]; norm_cast
  have hb2:v (D*b^2)=(d+2*B:ℤ) := by rw [v.map_mul,v.map_pow,hD,hb]; norm_cast
  have h4:v (4:F)=(2*e:ℤ) := by
    rw [show (4:F)=2*2 by ring,v.map_mul,h2]
    norm_cast; omega
  by_cases hs:v (a^2+D*b^2)≤(e+d:ℤ)
  · obtain ⟨s,hsv⟩ := finite_of_le _ (e+d) hs
    have hse:s≤e+d := by rw [hsv] at hs; exact_mod_cast hs
    have hF:v ((a^2+D*b^2)^2)=(2*s:ℤ) := by rw [v.map_pow,hsv]; norm_cast
    apply (min_le_left _ _).trans
    rw [hF]
    exact_mod_cast (show 2*s≤3*e+2*d by omega)
  · have hs' : ((e+d:ℤ):WithTop ℤ)<v (a^2+D*b^2) := lt_of_not_ge hs
    have hBz:B=0 := by
      by_contra hn
      have hAz:A=0 := by omega
      have hsum:v (a^2+D*b^2)=0 := by
        rw [v.map_add_eq_of_lt_left]
        · simpa [hAz] using ha2
        · rw [ha2,hb2,hAz]; exact_mod_cast (show 0<d+2*B by omega)
      rw [hsum] at hs'
      have hh:e+d<0 := by exact_mod_cast hs'
      omega
    have hb2' : v (D*b^2)=(d:ℤ) := by simpa [hBz] using hb2
    have hds : (d:WithTop ℤ)<v (a^2+D*b^2) :=
      lt_of_le_of_lt (by exact_mod_cast (show d≤e+d by omega)) hs'
    have haa : v (a^2)=(d:ℤ) := by
      have hh : v ((a^2+D*b^2)-D*b^2)=(d:ℤ) := by
        rw [v.map_sub_eq_of_lt_right]
        · exact hb2'
        · rw [hb2']; exact hds
      simpa only [add_sub_cancel_right] using hh
    have hAd:2*A=d := by rw [ha2] at haa; exact_mod_cast haa
    have htwo:v (2*D*b^2)=(e+d:ℤ) := by
      rw [v.map_mul,v.map_mul,v.map_pow,h2,hD,hb,hBz]
      simp
    have ht:v (a^2-D*b^2)=(e+d:ℤ) := by
      have hh : v ((a^2+D*b^2)-2*D*b^2)=(e+d:ℤ) := by
        rw [v.map_sub_eq_of_lt_right]
        · exact htwo
        · rw [htwo]; exact hs'
      convert hh using 1 <;> congr 1 <;> ring
    have hG:v (4*a*b*(a^2-D*b^2))=(3*e+A+d:ℤ) := by
      rw [v.map_mul,v.map_mul,v.map_mul,h4,ha,hb,ht,hBz]
      norm_cast; omega
    apply (min_le_right _ _).trans
    rw [hG]
    exact_mod_cast (show 3*e+A+d≤3*e+2*d by omega)

theorem primitive_universal_bound {F:Type*} [Field F] (v:AddValuation F (WithTop ℤ))
    (a b D:F) (d e:ℤ) (hD:v D=d) (h2:v (2:F)=e) (hd:0≤d) (he:0≤e)
    (hp:min (v a) (v b)=0) :
    min (v ((a^2+D*b^2)^2)) (v (4*a*b*(a^2-D*b^2)))≤(3*e+2*d:ℤ) := by
  by_cases haz:a=0
  · have hbz:v b=0 := by simpa [haz] using hp
    have hF:v ((a^2+D*b^2)^2)=(2*d:ℤ) := by
      simp [haz,v.map_pow,v.map_mul,hD,hbz]
      norm_cast
    apply (min_le_left _ _).trans
    rw [hF]; exact_mod_cast (show 2*d≤3*e+2*d by omega)
  by_cases hbz:b=0
  · have haz':v a=0 := by simpa [hbz] using hp
    have hF:v ((a^2+D*b^2)^2)=0 := by simp [hbz,v.map_pow,haz']
    apply (min_le_left _ _).trans
    rw [hF]; exact_mod_cast (show 0≤3*e+2*d by omega)
  obtain ⟨A,ha⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr haz)
  obtain ⟨B,hb⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr hbz)
  have hp' : min A B=0 := by rw [←ha,←hb] at hp; exact_mod_cast hp
  exact universal_gcd_bound v a b D A B d e ha.symm hb.symm hD h2
    (by omega) (by omega) hd he hp'

end DuplicationHeightLocal318
