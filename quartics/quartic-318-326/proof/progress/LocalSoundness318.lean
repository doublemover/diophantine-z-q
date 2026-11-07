module
public import ValuationTraceSelection
public import SourcePole318
public import FiveHeight49Weights
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public section

/-! A source-row bridge for the final 318 detector. No sourceArithmetic axiom.
The remaining inputs are explicitly the place, contact-weight values, even leaf
values, and the inherited pole obstruction at that place. -/
namespace LocalSoundness318
open ValuationNormChainExtraction
variable {K : Type*} [Field K]

/-- The trace row is used without an assumed inverse or nonzero real part. -/
theorem trace_nonzero (w wc n : K) (hw : w ≠ 0) (hc : wc ≠ 0)
    (htrace : n*(w+wc)=w*wc) : n ≠ 0 ∧ w+wc ≠ 0 := by
  have hh : n*(w+wc) ≠ 0 := by rw [htrace]; exact mul_ne_zero hw hc
  exact mul_ne_zero_iff.mp hh

/-- The source B row and the pole obstruction give precisely the strict
threshold needed by trace selection. The obstruction is needed only at B. -/
theorem pole_threshold (v : AddValuation K (WithTop ℤ))
    (eDelta n B : K) (R c : ℤ) (hR : Odd R)
    (he : v eDelta=(-R : ℤ)) (hn : v n=c)
    (hB : B*eDelta=n^2)
    (hpole : ∀ b : ℤ, v B=b → Odd b → 0≤b) :
    v B=(2*c+R : ℤ) ∧ 0<2*c+R := by
  have hn0 : n ≠ 0 := (v.ne_top_iff).mp (by rw [hn]; simp)
  have hB0 : B ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at hB
    exact pow_ne_zero 2 hn0 hB.symm
  obtain ⟨b,hb⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hB0)
  have hid := congrArg v hB
  rw [v.map_mul,v.map_pow,he,hn,←hb] at hid
  have hi : b-R=2*c := by exact_mod_cast hid
  have hbo : Odd b := by
    obtain ⟨r,hr⟩ := hR
    exact ⟨c+r,by omega⟩
  have hbn := hpole b hb.symm hbo
  have hpos : 0<b := by obtain ⟨r,hr⟩ := hbo; omega
  have heq : b=2*c+R := by omega
  exact ⟨by simpa only [heq] using hb.symm,by omega⟩

/-- Compose the actual field-valued chains, zero-leaf-safe valuation recursion,
actual trace equation and actual B equation. The conclusion selects one common
place for every leaf, not a potentially different place for each test. -/
theorem detector_extract (v : AddValuation K (WithTop ℤ)) (R : ℤ)
    (left right : List (Leaf K)) (eDelta n B : K)
    (hR : Odd R)
    (hl : ∀ p∈left,Spec v R p) (hr : ∀ p∈right,Spec v R p)
    (hml : ∀ p∈left,1≤p.order) (hmr : ∀ p∈right,1≤p.order)
    (he : v eDelta=(-R : ℤ))
    (htrace : n*(actual 1 left+actual 1 right)=actual 1 left*actual 1 right)
    (hB : B*eDelta=n^2)
    (hpole : ∀ b : ℤ, v B=b → Odd b → 0≤b) :
    0<R ∧ ((∀ p∈left,HasOrder p.order p.halfValue) ∨
      (∀ p∈right,HasOrder p.order p.halfValue)) := by
  let a := chain R 0 (numerical left)
  let b := chain R 0 (numerical right)
  have hva : v (actual 1 left)=a := value v R 0 left 1 hR hl (by simp)
  have hvb : v (actual 1 right)=b := value v R 0 right 1 hR hr (by simp)
  have hwa : actual 1 left ≠ 0 := (v.ne_top_iff).mp (by rw [hva]; simp)
  have hwb : actual 1 right ≠ 0 := (v.ne_top_iff).mp (by rw [hvb]; simp)
  have hn0 := (trace_nonzero _ _ n hwa hwb htrace).1
  obtain ⟨c,hc⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hn0)
  have ht := (pole_threshold v eDelta n B R c hR he hc.symm hB hpole).2
  rcases ValuationTraceSelection.one_place v _ _ n R a b c hva hvb hc.symm htrace ht with hleft|hright
  · obtain ⟨hp,hleaves⟩ := extract_actual_contact v R a left hR hl hml hva hleft
    exact ⟨hp,Or.inl hleaves⟩
  · obtain ⟨hp,hleaves⟩ := extract_actual_contact v R b right hR hr hmr hvb hright
    exact ⟨hp,Or.inr hleaves⟩

/-- At a unit delta the literal five-helper equations give exactly the required
order 1, 4, 13 weight valuations. This is not a borrowed old 8/29 formula. -/
theorem weight_values (v : AddValuation K (WithTop ℤ))
    (e q delta eDelta a c x y z : K) (R : ℤ)
    (he : e ≠ 0) (hve : v e=(-R : ℤ)) (hvd : v delta=0)
    (hqd : q*delta^3=e) (hEd : eDelta=e*delta)
    (ha : a=e^2) (hc : c*delta=a^2)
    (hx : x*eDelta=c^2) (hy : q*y=x^2) (hz : q*z=y^2) :
    v q=(-R : ℤ) ∧ v x=(-7*R : ℤ) ∧ v z=(-25*R : ℤ) ∧
      v eDelta=(-R : ℤ) := by
  obtain ⟨hxx,hyy,hzz⟩ := FiveHeight49Weights.outputs e q delta eDelta a c x y z
    he hqd hEd ha hc hx hy hz
  have hvq : v q=(-R : ℤ) := by
    have hh := congrArg v hqd
    simpa [v.map_mul,v.map_pow,hvd,hve] using hh
  refine ⟨hvq,?_,?_,?_⟩
  · rw [hxx,v.map_mul,v.map_pow,hvq,hve]
    norm_cast
    simp only [nsmul_eq_mul]
    norm_num
    ring
  · rw [hzz,v.map_mul,v.map_pow,hvq,hve]
    norm_cast
    simp only [nsmul_eq_mul]
    norm_num
    ring
  · simp [hEd,v.map_mul,hve,hvd]

/-- Doubling retains the honest group identity when the compressed H anchor
has its allowed two-torsion translate. -/
theorem doubled_anchor_identity {G : Type*} [AddCommGroup G]
    (P H R tau : G) (h c : ℤ) (hH : H=h • P+tau)
    (hR : R=c • P) (ht : (2:ℤ) • tau=0) :
    (2*h) • R=(2*c) • H := by
  have ht' : (2*c) • tau=0 := by
    calc
      (2*c) • tau=c • ((2:ℤ) • tau) := by rw [←mul_smul]; congr 1; ring
      _=0 := by rw [ht,smul_zero]
  rw [hH,hR,smul_add,ht',add_zero]
  simp only [←mul_smul]
  congr 1
  ring

/-- The final subtraction step recovers the root label from the two anchor
relations. It does not divide by h or h-1, or discard torsion. -/
theorem label_subtraction (L r s h u n : K)
    (hr : h*r=u) (hs : (h-1)*s=u-n) :
    L-n=h*(L-r)-(h-1)*(L-s) := by
  linear_combination hr-hs

/-- Integer arithmetic at the end of the scalar norm argument. -/
theorem scalar_even_rounding (a b : ℤ) (ha : Even a) (hb : Even b)
    (hsum : 30≤a+b) : 16≤a ∨ 16≤b := by
  obtain ⟨j,hj⟩ := ha
  obtain ⟨k,hk⟩ := hb
  omega

/-- Cross-comparison transfers integrality, including zero ratios. -/
theorem integral_of_difference (v : AddValuation K (WithTop ℤ)) (x y : K)
    (hy : 0≤v y) (hd : 0≤v (x-y)) : 0≤v x := by
  have hh := v.map_le_add hd hy
  simpa using hh

/-- An integral ratio converts the relative logarithm error to an absolute
error at the same precision. The actual analytic estimate remains an input. -/
theorem relative_error_absolute (v : AddValuation K (WithTop ℤ))
    (approx ratio factor : K) (k : ℤ)
    (heq : approx=ratio*factor) (hr : 0≤v ratio)
    (hf : (k : WithTop ℤ)≤v (factor-1)) :
    (k : WithTop ℤ)≤v (approx-ratio) := by
  have hid : approx-ratio=ratio*(factor-1) := by rw [heq]; ring
  rw [hid,v.map_mul]
  simpa using add_le_add hr hf

/-- Combine the two approximate integer-label equations without dividing by
h or h-1. This is the torsion-safe endpoint of the local ratio argument. -/
theorem label_congruence (v : AddValuation K (WithTop ℤ))
    (L r s h u n : K) (k : ℤ) (hr : h*r=u) (hs : (h-1)*s=u-n)
    (hh : 0≤v h) (hh1 : 0≤v (h-1))
    (hLr : (k : WithTop ℤ)≤v (L-r)) (hLs : (k : WithTop ℤ)≤v (L-s)) :
    (k : WithTop ℤ)≤v (L-n) := by
  rw [label_subtraction L r s h u n hr hs]
  apply v.map_le_sub
  · rw [v.map_mul]
    simpa using add_le_add hh hLr
  · rw [v.map_mul]
    simpa using add_le_add hh1 hLs

/-- Once the doubled identity is passed through the local logarithm, its
factor two cancels and gives the exact ratio. -/
theorem torsion_safe_log_ratio [CharZero K] (logR logH h c : K)
    (hh : h≠0) (hlogH : logH≠0)
    (heq : (2*h)*logR=(2*c)*logH) : logR/logH=c/h := by
  apply (div_eq_div_iff hlogH hh).mpr
  have h2 : (2:K)≠0 := by norm_num
  apply (mul_left_cancel₀ h2)
  linear_combination heq

/-- An intrinsically even leaf supplies the exact Spec used by the chain
bridge. The linear delta leaves need no global square root. -/
theorem leaf_spec_exists (v : AddValuation K (WithTop ℤ)) (R m : ℤ)
    (weight leaf : K) (hw : v weight=(-(2*m-1)*R : ℤ))
    (hl : ValuationEvenNormChain.EvenAt v leaf) :
    ∃ a : Option ℤ, Spec v R ⟨weight,leaf,m,a⟩ := by
  rcases hl with hz|⟨b,hb,j,hj⟩
  · exact ⟨none,hw,hz⟩
  · refine ⟨some j,hw,?_⟩
    change v leaf=(2*j : ℤ)
    rw [hb,hj]
    congr 1
    omega

/-- Full local detector extraction from the literal pole residuals. There is
no inherited pole-soundness assumption in this theorem. Number-field place
construction and source-specific contact/leaf instantiation are still required. -/
theorem source_detector_extract (v : AddValuation K (WithTop ℤ)) (R : ℤ)
    (left right : List (Leaf K)) (eDelta n B poleE poleP poleS poleQ poleH ss T : K)
    (hR : Odd R)
    (hl : ∀ p∈left,Spec v R p) (hr : ∀ p∈right,Spec v R p)
    (hml : ∀ p∈left,1≤p.order) (hmr : ∀ p∈right,1≤p.order)
    (he : v eDelta=(-R : ℤ))
    (htrace : n*(actual 1 left+actual 1 right)=actual 1 left*actual 1 right)
    (hB : B*eDelta=n^2)
    (h17 : v (17:K)=0) (h3 : v (3:K)=0)
    (hH : poleH=poleE*(17-B)) (hss : ss=poleS^2)
    (hT : T=(ss-poleH)*(ss+3*poleH))
    (hfirst : 17*poleP^2-289*B-578*poleE+34*poleH+51*poleE^2-3*poleE*poleH=0)
    (hsecond : 17*poleQ^2-B*T=0) :
    0<R ∧ ((∀ p∈left,HasOrder p.order p.halfValue) ∨
      (∀ p∈right,HasOrder p.order p.halfValue)) := by
  apply detector_extract v R left right eDelta n B hR hl hr hml hmr he htrace hB
  intro k hk hodd
  exact SourcePole318.source_no_negative_odd v B poleE poleP poleS poleQ poleH ss T
    k hk hodd h17 h3 hH hss hT hfirst hsecond

/-- Contact parity survives the fifth power of a square detector scale. -/
theorem contact_R_odd (f a : ℤ) (hf : Odd f) (ha : Even a) : Odd (f-5*a) := by
  obtain ⟨j,hj⟩ := hf
  obtain ⟨k,hk⟩ := ha
  exact ⟨j-5*k,by omega⟩

/-- Decode the contact parameter directly from e F=(A delta)^5.
At a consumed finite contact delta is a unit and the scale A is a square,
so R=f-5a is odd even when A is not a local unit. -/
theorem contact_e_value (v : AddValuation K (WithTop ℤ))
    (e F A delta : K) (a f : ℤ) (hA : v A=a) (hF : v F=f)
    (hd : v delta=0) (heq : e*F=(A*delta)^5) : v e=(5*a-f : ℤ) := by
  have hA0 : A≠0 := (v.ne_top_iff).mp (by rw [hA]; simp)
  have hd0 : delta≠0 := (v.ne_top_iff).mp (by rw [hd]; simp)
  have he0 : e≠0 := by
    intro hz
    rw [hz,zero_mul] at heq
    exact pow_ne_zero 5 (mul_ne_zero hA0 hd0) heq.symm
  obtain ⟨b,hb⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr he0)
  have hv := congrArg v heq
  rw [v.map_mul,v.map_pow,v.map_mul,hA,hF,hd,←hb,add_zero] at hv
  have hi : b+f=5*a := by exact_mod_cast hv
  have he : b=5*a-f := by omega
  simpa only [he] using hb.symm

end LocalSoundness318
