module
public import RawLucasOrientation318
public section
namespace ValuationLucasOrientation318
variable {F : Type*} [Field F]

theorem mul_positive (v : AddValuation F (WithTop ℤ)) (x y : F)
    (hx : 0<v x) (hy : 0≤v y) : 0<v (x*y) := by
  rw [v.map_mul]
  exact add_pos_of_pos_of_nonneg hx hy

theorem square_positive (v : AddValuation F (WithTop ℤ)) (x : F)
    (hx : 0<v x) : 0<v (x^2) := by
  simpa only [pow_two] using mul_positive v x x hx hx.le

theorem square_unit (v : AddValuation F (WithTop ℤ)) (x : F)
    (hx : v (x^2)=0) : v x=0 := by
  have hx0 : x≠0 := by intro hh; simp [hh] at hx
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hx0)
  rw [v.map_pow,←ha] at hx
  have ha0 : a=0 := by
    have hh : 2*a=0 := by exact_mod_cast hx
    omega
  simpa [ha0] using ha.symm

/-- This includes the u=0 point: it then forces y²=1 and y a unit. -/
theorem ordinate_unit (v : AddValuation F (WithTop ℤ)) (D u y : F)
    (hD : v D=0) (hu : 0<v u) (hcurve : y^2=1-D*u^4) : v y=0 := by
  have hu4 : 0<v (u^4) := by
    simpa only [show u^4=(u^2)^2 by ring] using square_positive v (u^2) (square_positive v u hu)
  have hDu : 0<v (D*u^4) := by rw [v.map_mul,hD,zero_add]; exact hu4
  apply square_unit v y
  rw [hcurve,v.map_sub_eq_of_lt_left (by simpa using hDu),v.map_one]

/-- No division or nonzero hypothesis is needed for the primary ratio row. -/
theorem primary_positive (v : AddValuation F (WithTop ℤ)) (D u y k A L : F)
    (hD : v D=0) (hk : v k=0) (hA : v A=0) (hu : 0<v u)
    (hcurve : y^2=1-D*u^4) (hr : k*y*L=u*A) : 0<v L := by
  have hy := ordinate_unit v D u y hD hu hcurve
  have hh := congrArg v hr
  simp only [v.map_mul,hk,hy,hA,zero_add,add_zero] at hh
  rwa [hh]

/-- The literal Lucas residual is a unit when all three primary ratios have
positive valuation. This is the source's orientation contradiction. -/
theorem lucas_unit (v : AddValuation F (WithTop ℤ)) (s t z : F)
    (h2 : 0≤v (2:F)) (hs : 0<v s) (ht : 0<v t) (hz : 0<v z) :
    v (t^2-s*(s-2)*t*z+(s-2)^2*z^2-1)=0 := by
  have hs2 : 0≤v (s-2) := v.map_le_sub hs.le h2
  have hfirst : 0<v (t^2) := square_positive v t ht
  have hsecond : 0<v (s*(s-2)*t*z) :=
    mul_positive v _ z (mul_positive v _ t (mul_positive v s (s-2) hs hs2) ht.le) hz.le
  have hsq : 0≤v ((s-2)^2) := by
    rw [v.map_pow,two_nsmul]; exact add_nonneg hs2 hs2
  have hthird : 0<v ((s-2)^2*z^2) := by
    rw [mul_comm]
    exact mul_positive v _ _ (square_positive v z hz) hsq
  have hsum : 0<v (t^2-s*(s-2)*t*z+(s-2)^2*z^2) :=
    v.map_lt_add (by rw [sub_eq_add_neg]; exact v.map_lt_add hfirst (by simpa using hsecond)) hthird
  rw [v.map_sub_eq_of_lt_right (by simpa using hsum),v.map_one]


open ConcreteG8Domain (K pair i)
open scoped QuadraticAlgebra
open CircuitReplay Raw318FinalReplay CompressedOrientation318 RawLucasOrientation318 RawDetector318

theorem good_m_unit (v : AddValuation K (WithTop ℤ))
    (h2 : v (2:K)=0) (h3 : v (3:K)=0) (h7 : v (7:K)=0)
    (h17 : v (17:K)=0) (h41 : v (41:K)=0) : v m=0 := by
  have hm := (good_constants v h2 h41).2
  have hi := root_unit v h2
  have h8 : v (8:K)=0 := by rw [show (8:K)=2^3 by norm_num,v.map_pow,h2]; simp
  have hc : SourceContact318.conj m=(39+36*i)/8 := by
    apply (eq_div_iff (by norm_num)).mpr
    ext <;> norm_num [SourceContact318.conj,m,i,pair]
  have hmc : 0≤v (SourceContact318.conj m) := by
    rw [hc,v.map_div,h8,sub_zero]
    apply v.map_le_add (nat_nonnegative v 39)
    rw [v.map_mul,hi,add_zero]
    exact nat_nonnegative v 36
  have hn : m*SourceContact318.conj m= -(3^2*7*17:K)/2^6 := by
    apply (eq_div_iff (by norm_num)).mpr
    ext <;> norm_num [SourceContact318.conj,m,pair]
  have hv := congrArg v hn
  simp only [v.map_mul,v.map_div,v.map_neg,v.map_pow,h2,h3,h7,h17] at hv
  norm_num at hv
  apply le_antisymm _ hm
  calc
    v m=v m+0 := by simp
    _≤v m+v (SourceContact318.conj m) := add_le_add (le_refl _) hmc
    _=0 := hv

theorem wrong_anchor_unit (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hk : v k=0) (hm : v m=0) (hD : v D=0)
    (hf : v (fH w)=0) (hg : 0<v (fV w)) : v (anchorA w)=0 := by
  obtain ⟨ht,hgrel⟩ := source_products S w source
  have hw : 0<v (shift w) := by
    apply CompressedOrientation318.positive_of_square v _
    simpa only [hgrel,v.map_mul,hf,zero_add] using hg
  have hmid : 0<v (mid w) := by rw [ht,v.map_mul,hf,zero_add]; exact hw
  have hkw : 0<v (k^2*shift w) := by
    simp only [v.map_mul,v.map_pow,hk,nsmul_zero,zero_add]
    exact hw
  have hDm : 0<v (D*mid w) := by rw [v.map_mul,hD,zero_add]; exact hmid
  have hsum : 0<v (k^2*shift w+D*mid w) := v.map_lt_add hkw hDm
  change v (m+k^2*shift w+D*mid w)=0
  rw [add_assoc,v.map_add_eq_of_lt_left (by rw [hm]; exact hsum),hm]

theorem wrong_direction_impossible (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hk : v k=0) (hm : v m=0) (hD : v D=0)
    (h2 : 0≤v (2:K)) (hf : v (fH w)=0) (hg : 0<v (fV w))
    (hu2 : 0<v (u2 w)) (hu3 : 0<v (u3 w)) (hu4 : 0<v (u4 w))
    (hLucas : 0<v (test15 S w)) : False := by
  have hA := wrong_anchor_unit S w source v hk hm hD hf hg
  have hL2 := primary_positive v D _ _ k _ _ hD hk hA hu2 (curve2 S w source) (ratio2 S w source)
  have hL3 := primary_positive v D _ _ k _ _ hD hk hA hu3 (curve3 S w source) (ratio3 S w source)
  have hL4 := primary_positive v D _ _ k _ _ hD hk hA hu4 (curve4 S w source) (ratio4 S w source)
  have hlu := lucas_unit v _ _ _ h2 hL2 hL3 hL4
  rw [lucas_actual S w source,hlu] at hLucas
  exact lt_irrefl _ hLucas

/-- The retained membership leaves and Lucas residual choose the H-positive
orientation directly from the literal source, not from an assumed formal log. -/
theorem source_selects_H (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hk : v k=0) (hm : v m=0) (hD : v D=0)
    (h2 : v (2:K)=0) (hor : 0<v (fH w) ∨ 0<v (fV w))
    (hb2 : 0<v (leaf2 S w)) (hb3 : 0<v (leaf3 S w)) (hb4 : 0<v (leaf4 S w))
    (hb15 : 0<v (leaf15 S w)) : 0<v (fH w) := by
  rcases hor with hf|hg
  · exact hf
  · have hf := (source_separates S w source v hk (by rw [hm]) (by rw [hD]) h2).2 hg
    exfalso
    apply wrong_direction_impossible S w source v hk hm hD (by rw [h2]) hf hg
    · apply CompressedOrientation318.positive_of_square v _
      simpa [leaf2_square S w source,test2,u2] using hb2
    · apply CompressedOrientation318.positive_of_square v _
      simpa [leaf3_square S w source,test3,u3] using hb3
    · apply CompressedOrientation318.positive_of_square v _
      simpa [leaf4_square S w source,test4,u4] using hb4
    · apply CompressedOrientation318.positive_of_square v _
      rwa [leaf15_square S w source] at hb15

end ValuationLucasOrientation318
