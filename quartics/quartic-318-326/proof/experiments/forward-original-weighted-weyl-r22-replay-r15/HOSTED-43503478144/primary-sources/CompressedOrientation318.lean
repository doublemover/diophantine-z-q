module
public import FiniteContact318
public section
namespace CompressedOrientation318
open ConcreteG8Domain CircuitReplay Raw318FinalReplay
open scoped QuadraticAlgebra
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The source compression alone separates the two formal directions.
No elliptic formal group or reduction homomorphism is assumed. -/
theorem other_unit {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (f g t k m D : F) (hk : v k=0) (hm : 0≤v m) (hD : 0≤v D)
    (h2 : v (2:F)=0) (ht : t^2=f*g)
    (he : 1=k^2*(f+g)+2*m*t+D*t^2) (hf : 0<v f) : v g=0 := by
  by_cases hf0 : f=0
  · have ht0 : t=0 := mul_self_eq_zero.mp (by simpa [hf0,pow_two] using ht)
    have he' : 1=k^2*g := by simpa [hf0,ht0] using he
    have hh := congrArg v he'
    simpa [v.map_mul,v.map_pow,hk] using hh.symm
  have hg0 : g≠0 := by
    intro hg
    have ht0 : t=0 := mul_self_eq_zero.mp (by simpa [hg,pow_two] using ht)
    have he' : 1=k^2*f := by simpa [hg,ht0] using he
    have hh := congrArg v he'
    have hfzero : v f=0 := by simpa [v.map_mul,v.map_pow,hk] using hh.symm
    simpa [hfzero] using hf
  have ht0 : t≠0 := by
    intro hz
    have hh : f*g=0 := by simpa [hz] using ht.symm
    exact (mul_ne_zero hf0 hg0) hh
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hf0)
  obtain ⟨b,hb⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hg0)
  obtain ⟨c,hc⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr ht0)
  have hap : 0<a := by rw [←ha] at hf; exact_mod_cast hf
  have hv := congrArg v ht
  rw [v.map_pow,v.map_mul,←ha,←hb,←hc] at hv
  have habc : 2*c=a+b := by exact_mod_cast hv
  have hka : v (k^2*f)=(a:ℤ) := by simp [v.map_mul,v.map_pow,hk,←ha]
  have hkb : v (k^2*g)=(b:ℤ) := by simp [v.map_mul,v.map_pow,hk,←hb]
  have hmt : (c:WithTop ℤ)≤v (2*m*t) := by
    simp only [v.map_mul,h2,zero_add,←hc]
    simpa using add_le_add hm (le_refl (c:WithTop ℤ))
  have hdt : (2*c:ℤ)≤v (D*t^2) := by
    simp only [v.map_mul,v.map_pow,←hc]
    have hh := add_le_add hD (le_refl (2 • (c:WithTop ℤ)))
    have hco : 2 • (c:WithTop ℤ)=((2*c:ℤ):WithTop ℤ) := by simp only [two_nsmul]; norm_cast; ring
    rw [hco] at hh ⊢
    simpa only [zero_add] using hh
  let other := k^2*f+2*m*t+D*t^2
  have hei : 1=k^2*g+other := by dsimp [other]; linear_combination he
  by_cases hbn : b<0
  · have hlt : (b:WithTop ℤ)<v other := by
      apply v.map_lt_add
      · apply v.map_lt_add
        · rw [hka]; exact_mod_cast (show b<a by omega)
        · exact lt_of_lt_of_le (by exact_mod_cast (show b<c by omega)) hmt
      · exact lt_of_lt_of_le (by exact_mod_cast (show b<2*c by omega)) hdt
    have hh := congrArg v hei
    rw [v.map_one,v.map_add_eq_of_lt_left (by rw [hkb]; exact hlt),hkb] at hh
    have hbzero : b=0 := by exact_mod_cast hh.symm
    omega
  · have hother : 0<v other := by
      apply v.map_lt_add
      · apply v.map_lt_add
        · rw [hka]; exact_mod_cast hap
        · exact lt_of_lt_of_le (by exact_mod_cast (show 0<c by omega)) hmt
      · exact lt_of_lt_of_le (by exact_mod_cast (show 0<2*c by omega)) hdt
    have hekg : k^2*g=1-other := by linear_combination -hei
    have hh := congrArg v hekg
    rw [hkb,v.map_sub_eq_of_lt_left (by simpa using hother),v.map_one] at hh
    exact hb.symm.trans hh

@[expose] def k : K := pair (-1) (7/4)
@[expose] def m : K := pair (39/8) (-9/2)
@[expose] def D : K := pair 11 (-6)
@[expose] def fH (w : Assignment) : K := pair (w 33) (w 34)
@[expose] def shift (w : Assignment) : K := pair (w 35) (w 36)
@[expose] def mid (w : Assignment) : K := pair (w 74) (w 75)
@[expose] def fV (w : Assignment) : K := pair (w 76) (w 77)

theorem source_relations (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (mid w)^2=fH w*fV w ∧ 1=k^2*(fH w+fV w)+2*m*mid w+D*(mid w)^2 := by
  have h32 := source _ (List.getElem_mem (l:=stage0 S) (n:=32) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h33 := source _ (List.getElem_mem (l:=stage0 S) (n:=33) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h34 := source _ (List.getElem_mem (l:=stage0 S) (n:=34) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h35 := source _ (List.getElem_mem (l:=stage0 S) (n:=35) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h36 := source _ (List.getElem_mem (l:=stage0 S) (n:=36) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have h37 := source _ (List.getElem_mem (l:=stage0 S) (n:=37) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  change r32 S w=0 at h32; change r33 S w=0 at h33
  change r34 S w=0 at h34; change r35 S w=0 at h35
  change r36 S w=0 at h36; change r37 S w=0 at h37
  have ht : mid w=fH w*shift w := by
    ext <;> norm_num [mid,fH,shift,pair]
    · dsimp only [r32] at h32; linear_combination h32
    · dsimp only [r33] at h33; linear_combination h33
  have hg : fV w=mid w*shift w := by
    ext <;> norm_num [fV,mid,shift,pair]
    · dsimp only [r34] at h34; linear_combination h34
    · dsimp only [r35] at h35; linear_combination h35
  constructor
  · rw [hg,ht]; ring
  · ext <;> norm_num [k,m,D,fH,fV,mid,pair,pow_two]
    · dsimp only [r36] at h36; linear_combination h36
    · dsimp only [r37] at h37; linear_combination h37

theorem source_separates (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hk : v k=0) (hm : 0≤v m)
    (hD : 0≤v D) (h2 : v (2:K)=0) :
    (0<v (fH w) → v (fV w)=0) ∧ (0<v (fV w) → v (fH w)=0) := by
  obtain ⟨ht,he⟩ := source_relations S w source
  constructor
  · exact other_unit v _ _ _ k m D hk hm hD h2 ht he
  · exact other_unit v _ _ _ k m D hk hm hD h2 (by simpa [mul_comm] using ht)
      (by simpa only [add_comm (fH w) (fV w)] using he)


theorem nat_nonnegative (v : AddValuation K (WithTop ℤ)) (n : ℕ) : 0≤v (n:K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one]
    exact v.map_le_add ih (by simp)

theorem root_unit (v : AddValuation K (WithTop ℤ)) (h2 : v (2:K)=0) : v i=0 := by
  have hi0 : i≠0 := by intro h; have hh := congrArg QuadraticAlgebra.im h; norm_num [i,pair] at hh
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hi0)
  have hh := congrArg v i_square
  rw [v.map_pow,←ha,h2] at hh
  have ha0 : a=0 := by
    have he : 2*a=0 := by exact_mod_cast hh
    omega
  simpa [ha0] using ha.symm

/-- Actual generator coefficients, with only their true denominator and norm
primes excluded. -/
theorem good_constants (v : AddValuation K (WithTop ℤ)) (h2 : v (2:K)=0)
    (h41 : v (41:K)=0) : v k=0 ∧ 0≤v m := by
  have hi := root_unit v h2
  have h4 : v (4:K)=0 := by
    rw [show (4:K)=2^2 by norm_num,v.map_pow,h2]; simp
  have h8 : v (8:K)=0 := by
    rw [show (8:K)=2^3 by norm_num,v.map_pow,h2]; simp
  have h7i : 0≤v (7*i) := by
    rw [v.map_mul,hi,add_zero]; exact nat_nonnegative v 7
  have h36i : 0≤v (36*i) := by
    rw [v.map_mul,hi,add_zero]; exact nat_nonnegative v 36
  have hkexpr : k=(-4+7*i)/4 := by
    apply (eq_div_iff (by norm_num)).mpr
    ext <;> norm_num [k,i,pair]
  have hkc : SourceContact318.conj k=(-4-7*i)/4 := by
    apply (eq_div_iff (by norm_num)).mpr
    ext <;> norm_num [SourceContact318.conj,k,i,pair]
  have hmexpr : m=(39-36*i)/8 := by
    apply (eq_div_iff (by norm_num)).mpr
    ext <;> norm_num [m,i,pair]
  have hkp : 0≤v k := by
    rw [hkexpr,v.map_div,h4,sub_zero]
    exact v.map_le_add (by simpa using nat_nonnegative v 4) h7i
  have hkcp : 0≤v (SourceContact318.conj k) := by
    rw [hkc,v.map_div,h4,sub_zero]
    exact v.map_le_sub (by simpa using nat_nonnegative v 4) h7i
  have hn : k*SourceContact318.conj k=-(41:K)/8 := by
    apply (eq_div_iff (by norm_num)).mpr
    ext <;> norm_num [SourceContact318.conj,k,pair]
  have hv := congrArg v hn
  rw [v.map_mul,v.map_div,v.map_neg,h41,h8] at hv
  norm_num at hv
  constructor
  · apply le_antisymm _ hkp
    calc
      v k=v k+0 := by simp
      _≤v k+v (SourceContact318.conj k) := add_le_add (le_refl _) hkcp
      _=0 := hv
  · rw [hmexpr,v.map_div,h8,sub_zero]
    exact v.map_le_sub (nat_nonnegative v 39) h36i

theorem positive_of_square (v : AddValuation K (WithTop ℤ)) (z : K)
    (h : 0<v (z^2)) : 0<v z := by
  by_contra! hn
  rw [v.map_pow,two_nsmul] at h
  exact not_lt_of_ge (add_nonpos hn hn) h

/-- A valuation-only orientation certificate for two split places. -/
theorem opposite (a b c d : WithTop ℤ) (hab : 0<a+b) (hcd : 0<c+d)
    (hac : 0<a → c=0) (hca : 0<c → a=0)
    (hbd : 0<b → d=0) (hdb : 0<d → b=0) :
    (0<a ∧ b=0 ∧ c=0 ∧ 0<d) ∨ (a=0 ∧ 0<b ∧ 0<c ∧ d=0) := by
  by_cases ha : 0<a
  · have hc := hac ha
    have hd : 0<d := by simpa [hc] using hcd
    exact Or.inl ⟨ha,hdb hd,hc,hd⟩
  · have hb : 0<b := by
      by_contra! hb
      exact not_lt_of_ge (add_nonpos (le_of_not_gt ha) hb) hab
    have hd := hbd hb
    have hc : 0<c := by simpa [hd] using hcd
    exact Or.inr ⟨hca hc,hb,hc,hd⟩

open ConcretePadic318 SourcePadic318
/-- Actual split-place separation from the literal source and positive norm
tests. This proves the opposite formal directions without an elliptic-group
reduction theorem; choosing which direction satisfies the Lucas tests is later. -/
theorem source_opposite_at_split (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (hp2 : ¬p∣2) (hp3 : ¬p∣3) (hp7 : ¬p∣7) (hp41 : ¬p∣41)
    (hH : 0<rationalPlace p ((w 33)^2-2*(w 34)^2))
    (hV : 0<rationalPlace p ((w 76)^2-2*(w 77)^2)) :
    (0<place p rho hr (fH w) ∧ place p (-rho) (negative_root p rho hr) (fH w)=0 ∧
      place p rho hr (fV w)=0 ∧ 0<place p (-rho) (negative_root p rho hr) (fV w)) ∨
    (place p rho hr (fH w)=0 ∧ 0<place p (-rho) (negative_root p rho hr) (fH w) ∧
      0<place p rho hr (fV w) ∧ place p (-rho) (negative_root p rho hr) (fV w)=0) := by
  have separate (r : ℚ_[p]) (hroot : r^2=2) :
      (0<place p r hroot (fH w) → place p r hroot (fV w)=0) ∧
      (0<place p r hroot (fV w) → place p r hroot (fH w)=0) := by
    have h2 := place_nat_unit p r hroot 2 hp2
    have h3 := place_nat_unit p r hroot 3 hp3
    have h7 := place_nat_unit p r hroot 7 hp7
    have h41 := place_nat_unit p r hroot 41 hp41
    obtain ⟨hk,hm⟩ := good_constants (place p r hroot) h2 h41
    have hD := (discriminant_units (place p r hroot) h2 h3 h7).2
    exact source_separates S w source _ hk hm (by change 0≤place p r hroot (pair 11 (-6)); rw [hD]) h2
  have hleft := separate rho hr
  have hright := separate (-rho) (negative_root p rho hr)
  apply opposite _ _ _ _ _ _ hleft.1 hleft.2 hright.1 hright.2
  · change 0<place p rho hr (pair (w 33) (w 34))+place p (-rho) (negative_root p rho hr) (pair (w 33) (w 34))
    rw [norm_valuation]; exact hH
  · change 0<place p rho hr (pair (w 76) (w 77))+place p (-rho) (negative_root p rho hr) (pair (w 76) (w 77))
    rw [norm_valuation]; exact hV


open RawDetector318 SourceContact318

theorem source_norm_tests (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ))
    (h0 : (8:WithTop ℤ)≤v (leaf0 S w)) (h5 : (2:WithTop ℤ)≤v (leaf5 S w)) :
    0<rational v ((w 33)^2-2*(w 34)^2) ∧
      0<rational v ((w 76)^2-2*(w 77)^2) := by
  have h38 : r38 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=38)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hn : (w 37)^2=(w 33)^2-2*(w 34)^2 := by
    dsimp only [r38] at h38; linear_combination h38
  have hleaf0 : leaf0 S w=pair ((w 33)^2-2*(w 34)^2) 0 := by
    rw [leaf0_square S w source]
    ext <;> norm_num [test0,pair,pow_two]
    nlinarith [hn]
  have hleaf5 : leaf5 S w=(pair ((w 76)^2-2*(w 77)^2) 0)^2 := by
    rw [leaf5_square S w source]
    apply congrArg (fun x : K => x^2)
    apply QuadraticAlgebra.ext <;> dsimp only [test5,pair] <;> ring
  constructor
  · change 0<v (pair ((w 33)^2-2*(w 34)^2) 0)
    rw [←hleaf0]
    exact lt_of_lt_of_le (by norm_num) h0
  · change 0<v (pair ((w 76)^2-2*(w 77)^2) 0)
    apply positive_of_square v _
    rw [←hleaf5]
    exact lt_of_lt_of_le (by norm_num) h5

theorem common_place_norm_tests (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (ps : List (K×K×ℤ)) (q0 q5 : K)
    (h0mem : (q0,leaf0 S w,4)∈ps) (h5mem : (q5,leaf5 S w,1)∈ps)
    (hb : (∀x∈ps,(2*x.2.2:ℤ)≤v x.2.1) ∨
      (∀x∈ps,(2*x.2.2:ℤ)≤v (SourceContact318.conj x.2.1))) :
    0<rational v ((w 33)^2-2*(w 34)^2) ∧
      0<rational v ((w 76)^2-2*(w 77)^2) := by
  have hc0 : SourceContact318.conj (leaf0 S w)=leaf0 S w := by simp [leaf0]
  have hc5 : SourceContact318.conj (leaf5 S w)=leaf5 S w := by simp [leaf5]
  rcases hb with hb|hb
  · exact source_norm_tests S w source v (by simpa using hb _ h0mem) (by simpa using hb _ h5mem)
  · exact source_norm_tests S w source v (by simpa [hc0] using hb _ h0mem)
      (by simpa [hc5] using hb _ h5mem)

/-- The actual selected-contact theorem already supplies both positive norms;
no group-membership or local orientation premise is needed for this step. -/
theorem contact0_norm_positive (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ)
    (hA : rationalPlace p (RawWeights318.A0 S w)=a)
    (hF : rationalPlace p (RawWeights318.F0 S w)=f)
    (hd : rationalPlace p (RawWeights318.delta0 S w)=0) (hf : Odd f)
    (hp2 : ¬p∣2) (hp3 : ¬p∣3) (hp7 : ¬p∣7) (hp17 : ¬p∣17) :
    0<rationalPlace p ((w 33)^2-2*(w 34)^2) ∧
      0<rationalPlace p ((w 76)^2-2*(w 77)^2) := by
  have hD := discriminant_units (place p rho hr) (place_nat_unit p rho hr 2 hp2)
    (place_nat_unit p rho hr 3 hp3) (place_nat_unit p rho hr 7 hp7)
  have hb := (SourceContact318.contact0_extract S w source (place p rho hr) a f
    (by simpa only [rational_place] using hA) (by simpa only [rational_place] using hF)
    (by simpa only [rational_place] using hd) hf hD.1 hD.2
    (place_nat_unit p rho hr 2 hp2) (place_nat_unit p rho hr 3 hp3) (place_nat_unit p rho hr 17 hp17)).2
  have hh := common_place_norm_tests S w source (place p rho hr) (inputs0 S w)
    (q0_4 S w) (q0_1 S w) (by simp [inputs0]) (by simp [inputs0]) hb
  simpa only [rational_place] using hh

/-- The actual selected-contact theorem already supplies both positive norms;
no group-membership or local orientation premise is needed for this step. -/
theorem contact1_norm_positive (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ)
    (hA : rationalPlace p (RawWeights318.A1 S w)=a)
    (hF : rationalPlace p (RawWeights318.F1 S w)=f)
    (hd : rationalPlace p (RawWeights318.delta1 S w)=0) (hf : Odd f)
    (hp2 : ¬p∣2) (hp3 : ¬p∣3) (hp7 : ¬p∣7) (hp17 : ¬p∣17) :
    0<rationalPlace p ((w 33)^2-2*(w 34)^2) ∧
      0<rationalPlace p ((w 76)^2-2*(w 77)^2) := by
  have hD := discriminant_units (place p rho hr) (place_nat_unit p rho hr 2 hp2)
    (place_nat_unit p rho hr 3 hp3) (place_nat_unit p rho hr 7 hp7)
  have hb := (SourceContact318.contact1_extract S w source (place p rho hr) a f
    (by simpa only [rational_place] using hA) (by simpa only [rational_place] using hF)
    (by simpa only [rational_place] using hd) hf hD.1 hD.2
    (place_nat_unit p rho hr 2 hp2) (place_nat_unit p rho hr 3 hp3) (place_nat_unit p rho hr 17 hp17)).2
  have hh := common_place_norm_tests S w source (place p rho hr) (inputs1 S w)
    (q1_4 S w) (q1_1 S w) (by simp [inputs1]) (by simp [inputs1]) hb
  simpa only [rational_place] using hh

/-- The actual selected-contact theorem already supplies both positive norms;
no group-membership or local orientation premise is needed for this step. -/
theorem contact2_norm_positive (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ)
    (hA : rationalPlace p (RawWeights318.A2 S w)=a)
    (hF : rationalPlace p (RawWeights318.F2 S w)=f)
    (hd : rationalPlace p (RawWeights318.delta2 S w)=0) (hf : Odd f)
    (hp2 : ¬p∣2) (hp3 : ¬p∣3) (hp7 : ¬p∣7) (hp17 : ¬p∣17) :
    0<rationalPlace p ((w 33)^2-2*(w 34)^2) ∧
      0<rationalPlace p ((w 76)^2-2*(w 77)^2) := by
  have hD := discriminant_units (place p rho hr) (place_nat_unit p rho hr 2 hp2)
    (place_nat_unit p rho hr 3 hp3) (place_nat_unit p rho hr 7 hp7)
  have hb := (SourceContact318.contact2_extract S w source (place p rho hr) a f
    (by simpa only [rational_place] using hA) (by simpa only [rational_place] using hF)
    (by simpa only [rational_place] using hd) hf hD.1 hD.2
    (place_nat_unit p rho hr 2 hp2) (place_nat_unit p rho hr 3 hp3) (place_nat_unit p rho hr 17 hp17)).2
  have hh := common_place_norm_tests S w source (place p rho hr) (inputs2 S w)
    (q2_4 S w) (q2_1 S w) (by simp [inputs2]) (by simp [inputs2]) hb
  simpa only [rational_place] using hh


@[expose] def OppositeAt (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2) (w : Assignment) : Prop :=
    (0<place p rho hr (fH w) ∧ place p (-rho) (negative_root p rho hr) (fH w)=0 ∧
      place p rho hr (fV w)=0 ∧ 0<place p (-rho) (negative_root p rho hr) (fV w)) ∨
    (place p rho hr (fH w)=0 ∧ 0<place p (-rho) (negative_root p rho hr) (fH w) ∧
      0<place p rho hr (fV w) ∧ place p (-rho) (negative_root p rho hr) (fV w)=0)
open FiniteContact318 RawWeights318

/-- Full source-to-opposite-place certificate for the actual selected contact. -/
theorem source_contact0_opposite (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hA : rationalPlace p (A0 S w)=a)
    (hf : rationalPlace p (t0 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    OppositeAt p rho hr w := by
  have hp2 := not_dvd_supported p hgood 2 (by norm_num [contactModulus])
  have hp3 := not_dvd_supported p hgood 3 (by norm_num [contactModulus])
  have hp7 := not_dvd_supported p hgood 7 (by norm_num [contactModulus])
  obtain ⟨hF,hd⟩ := selected_contact p hgood (t0 S w) j f hf hpos
  obtain ⟨hH,hV⟩ := contact0_norm_positive p rho hr S w source a f hA
    (by rw [F0_actual S w source]; exact hF) hd hodd hp2 hp3 hp7 hp17
  exact source_opposite_at_split p rho hr S w source hp2 hp3 hp7 hp41 hH hV

/-- Full source-to-opposite-place certificate for the actual selected contact. -/
theorem source_contact1_opposite (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hA : rationalPlace p (A1 S w)=a)
    (hf : rationalPlace p (t1 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    OppositeAt p rho hr w := by
  have hp2 := not_dvd_supported p hgood 2 (by norm_num [contactModulus])
  have hp3 := not_dvd_supported p hgood 3 (by norm_num [contactModulus])
  have hp7 := not_dvd_supported p hgood 7 (by norm_num [contactModulus])
  obtain ⟨hF,hd⟩ := selected_contact p hgood (t1 S w) j f hf hpos
  obtain ⟨hH,hV⟩ := contact1_norm_positive p rho hr S w source a f hA
    (by rw [F1_actual S w source]; exact hF) hd hodd hp2 hp3 hp7 hp17
  exact source_opposite_at_split p rho hr S w source hp2 hp3 hp7 hp41 hH hV

/-- Full source-to-opposite-place certificate for the actual selected contact. -/
theorem source_contact2_opposite (p : ℕ) [Fact p.Prime] (rho : ℚ_[p]) (hr : rho^2=2)
    (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) (a f : ℤ) (j : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17) (hp41 : ¬p∣41)
    (hA : rationalPlace p (A2 S w)=a)
    (hf : rationalPlace p (t2 S w-root j)=f) (hpos : 0<f) (hodd : Odd f) :
    OppositeAt p rho hr w := by
  have hp2 := not_dvd_supported p hgood 2 (by norm_num [contactModulus])
  have hp3 := not_dvd_supported p hgood 3 (by norm_num [contactModulus])
  have hp7 := not_dvd_supported p hgood 7 (by norm_num [contactModulus])
  obtain ⟨hF,hd⟩ := selected_contact p hgood (t2 S w) j f hf hpos
  obtain ⟨hH,hV⟩ := contact2_norm_positive p rho hr S w source a f hA
    (by rw [F2_actual S w source]; exact hF) hd hodd hp2 hp3 hp7 hp17
  exact source_opposite_at_split p rho hr S w source hp2 hp3 hp7 hp41 hH hV

end CompressedOrientation318
