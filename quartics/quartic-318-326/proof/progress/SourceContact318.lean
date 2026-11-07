module
public import RawWeights318
public import RawSourcePole318
public section
namespace SourceContact318
open ConcreteG8Domain CircuitReplay Raw318FinalReplay ValuationNormChainExtraction
open scoped QuadraticAlgebra
set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[expose] def conj : K →+* K where
  toFun x := pair x.re (-x.im)
  map_zero' := by ext <;> simp [pair]
  map_one' := by ext <;> simp [pair]
  map_add' x y := by ext <;> simp [pair] <;> ring
  map_mul' x y := by ext <;> simp [pair] <;> ring

@[simp] theorem conj_pair (a b : ℚ) : conj (pair a b)=pair a (-b) := rfl
@[simp] theorem conj_rational (a : ℚ) : conj (pair a 0)=pair a 0 := by simp

@[expose] noncomputable def rational (v : AddValuation K (WithTop ℤ)) : AddValuation ℚ (WithTop ℤ) :=
  v.comap (algebraMap ℚ K)
@[simp] theorem rational_apply (v : AddValuation K (WithTop ℤ)) (a : ℚ) :
    rational v a=v (pair a 0) := rfl

@[expose] def HalfValue (v : AddValuation K (WithTop ℤ)) (x : K) : Option ℤ → Prop
  | none => x=0
  | some a => v x=(2*a:ℤ)

theorem exists_half (v : AddValuation K (WithTop ℤ)) (x : K)
    (h : ValuationEvenNormChain.EvenAt v x) : ∃a,HalfValue v x a := by
  rcases h with hz|⟨b,hb,j,hj⟩
  · exact ⟨none,hz⟩
  · refine ⟨some j,?_⟩
    change v x=(2*j:ℤ)
    rw [hb,hj]
    congr 1
    omega

@[expose] noncomputable def half (v : AddValuation K (WithTop ℤ)) (x : K) : Option ℤ := by
  classical
  exact if h : ∃a,HalfValue v x a then Classical.choose h else none

theorem half_spec (v : AddValuation K (WithTop ℤ)) (x : K)
    (h : ValuationEvenNormChain.EvenAt v x) : HalfValue v x (half v x) := by
  classical
  simp only [half,dite_eq_left (exists_half v x h)]
  exact Classical.choose_spec (exists_half v x h)

@[expose] noncomputable def tag (v : AddValuation K (WithTop ℤ)) (p : K×K×ℤ) : Leaf K :=
  ⟨p.1,p.2.1,p.2.2,half v p.2.1⟩

theorem tag_spec (v : AddValuation K (WithTop ℤ)) (R : ℤ) (p : K×K×ℤ)
    (hw : v p.1=(-(2*p.2.2-1)*R:ℤ))
    (he : ValuationEvenNormChain.EvenAt v p.2.1) : Spec v R (tag v p) :=
  ⟨hw,half_spec v _ he⟩

theorem tag_bound (v : AddValuation K (WithTop ℤ)) (p : K×K×ℤ)
    (he : ValuationEvenNormChain.EvenAt v p.2.1)
    (hh : HasOrder (tag v p).order (tag v p).halfValue) :
    (2*p.2.2:ℤ)≤v p.2.1 := by
  have hs := half_spec v _ he
  change HasOrder p.2.2 (half v p.2.1) at hh
  cases hv : half v p.2.1 with
  | none => simp only [hv,HalfValue] at hs; simp [hs]
  | some a =>
    simp only [hv,HalfValue] at hs
    simp only [hv,HasOrder] at hh
    rw [hs]
    exact_mod_cast (show 2*p.2.2≤2*a by omega)

@[expose] def eval (initial : K) (ps : List (K×K×ℤ)) : K :=
  ps.foldl (fun x p=>x^2+p.1*p.2.1) initial
@[expose] def conjugate (p : K×K×ℤ) : K×K×ℤ := (conj p.1,conj p.2.1,p.2.2)

theorem actual_tag (v : AddValuation K (WithTop ℤ)) (ps : List (K×K×ℤ)) (initial : K) :
    actual initial (ps.map (tag v))=eval initial ps := by
  simp only [actual,List.foldl_map,eval,tag]

theorem eval_conjugate (ps : List (K×K×ℤ)) (initial : K) :
    eval (conj initial) (ps.map conjugate)=conj (eval initial ps) := by
  induction ps generalizing initial with
  | nil => simp [eval]
  | cons p ps ih =>
    change eval ((conj initial)^2+conj p.1*conj p.2.1) (ps.map conjugate)=_
    rw [←conj.map_pow,←conj.map_mul,←conj.map_add]
    exact ih _

/-- Full extraction needs neither chosen nonzero leaves nor a presumed
positive contact parameter. Both follow from the actual source trace and B row. -/
theorem extract (v : AddValuation K (WithTop ℤ)) (R : ℤ) (ps : List (K×K×ℤ))
    (eDelta n B : K) (hR : Odd R)
    (hw : ∀p∈ps,v p.1=(-(2*p.2.2-1)*R:ℤ))
    (hwc : ∀p∈ps,v (conj p.1)=(-(2*p.2.2-1)*R:ℤ))
    (he : ∀p∈ps,ValuationEvenNormChain.EvenAt v p.2.1)
    (hec : ∀p∈ps,ValuationEvenNormChain.EvenAt v (conj p.2.1))
    (hm : ∀p∈ps,1≤p.2.2)
    (hed : v eDelta=(-R:ℤ))
    (ht : n*(eval 1 ps+conj (eval 1 ps))=eval 1 ps*conj (eval 1 ps))
    (hB : B*eDelta=n^2)
    (hpole : ∀b:ℤ,v B=b→Odd b→0≤b) :
    0<R ∧ ((∀p∈ps,(2*p.2.2:ℤ)≤v p.2.1) ∨
      (∀p∈ps,(2*p.2.2:ℤ)≤v (conj p.2.1))) := by
  have hs : ∀p∈ps.map (tag v),Spec v R p := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact tag_spec v R q (hw q hq) (he q hq)
  have hsc : ∀p∈(ps.map conjugate).map (tag v),Spec v R p := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    exact tag_spec v R _ (hwc r hr) (hec r hr)
  have hm1 : ∀p∈ps.map (tag v),1≤p.order := by
    intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact hm q hq
  have hm2 : ∀p∈(ps.map conjugate).map (tag v),1≤p.order := by
    intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq; exact hm r hr
  have hlval := actual_tag v ps (1:K)
  have hrval : actual 1 ((ps.map conjugate).map (tag v))=conj (eval 1 ps) := by
    calc
      actual 1 ((ps.map conjugate).map (tag v))=eval (conj 1) (ps.map conjugate) := by rw [actual_tag,conj.map_one]
      _=conj (eval 1 ps) := eval_conjugate ps 1
  have hh := LocalSoundness318.detector_extract v R _ _ eDelta n B hR hs hsc hm1 hm2 hed
    (by rw [hlval,hrval]; exact ht) hB hpole
  refine ⟨hh.1,?_⟩
  rcases hh.2 with hl|hr
  · left; intro p hp
    exact tag_bound v p (he p hp) (hl _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  · right; intro p hp
    exact tag_bound v (conjugate p) (hec p hp)
      (hr _ (List.mem_map.mpr ⟨conjugate p,List.mem_map.mpr ⟨p,hp,rfl⟩,rfl⟩))
theorem eval_forget (ps : List (K×K×ℤ)) (initial : K) :
    eval initial ps=(ps.map (fun p=>(p.1,p.2.1))).foldl (fun x p=>x^2+p.1*p.2) initial := by
  simp only [eval,List.foldl_map]

theorem conj_even (v : AddValuation K (WithTop ℤ)) (x : K)
    (h : ValuationEvenNormChain.EvenAt (v.comap conj) x) :
    ValuationEvenNormChain.EvenAt v (conj x) := by
  rcases h with hz|⟨a,ha,ho⟩
  · left; rw [hz,conj.map_zero]
  · exact Or.inr ⟨a,ha,ho⟩

theorem square_value_even {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (x : F) (a : ℤ) (h : v (x^2)=a) : Even a := by
  rcases ValuationEvenNormChain.square_even v x with hz|⟨b,hb,he⟩
  · rw [hz,v.map_zero] at h
    exact False.elim (WithTop.top_ne_coe h)
  · have hab : a=b := by rw [h] at hb; exact_mod_cast hb
    simpa only [hab] using he

-- BEGIN GENERATED CONTACT
open RawDetector318 RawWeights318

theorem all_even (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (hD : v (pair 11 6)=0) (h2 : v (2:K)=0) :
    ValuationEvenNormChain.EvenAt v (leaf0 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf1 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf2 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf3 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf4 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf5 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf6 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf7 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf8 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf9 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf10 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf11 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf12 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf13 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf14 S w) ∧
    ValuationEvenNormChain.EvenAt v (leaf15 S w) := by
  exact ⟨leaf0_even S w source v hD h2,leaf1_even S w source v hD h2,leaf2_even S w source v hD h2,leaf3_even S w source v hD h2,leaf4_even S w source v hD h2,leaf5_even S w source v hD h2,leaf6_even S w source v hD h2,leaf7_even S w source v hD h2,leaf8_even S w source v hD h2,leaf9_even S w source v hD h2,leaf10_even S w source v hD h2,leaf11_even S w source v hD h2,leaf12_even S w source v hD h2,leaf13_even S w source v hD h2,leaf14_even S w source v hD h2,leaf15_even S w source v hD h2⟩

@[expose] def inputs0 (S : ℚ) (w : Assignment) : List (K×K×ℤ) := [(q0_4 S w,leaf0 S w,4), (q0_1 S w,leaf5 S w,1), (q0_1 S w,leaf1 S w,1), (q0_1 S w,leaf2 S w,1), (q0_1 S w,leaf3 S w,1), (q0_1 S w,leaf4 S w,1), (q0_1 S w,leaf6 S w,1), (q0_1 S w,leaf7 S w,1), (q0_1 S w,leaf8 S w,1), (q0_1 S w,leaf9 S w,1), (q0_4 S w,leaf10 S w,4), (q0_13 S w,leaf11 S w,13), (q0_13 S w,leaf12 S w,13), (q0_13 S w,leaf13 S w,13), (q0_4 S w,leaf14 S w,4), (q0_13 S w,leaf15 S w,13)]
theorem eval0_actual (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    eval 1 (inputs0 S w)=node0_15 S w := by
  rw [eval_forget]
  have heq : (inputs0 S w).map (fun p=>(p.1,p.2.1))=detector0_leaves S w := rfl
  rw [heq]
  exact detector0_actual S w source

theorem contact0_extract (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (a f : ℤ)
    (hA : rational v (A0 S w)=a) (hF : rational v (F0 S w)=f)
    (hd : rational v (delta0 S w)=0) (hf : Odd f)
    (hD : v (pair 11 6)=0) (hDc : v (pair 11 (-6))=0)
    (h2 : v (2:K)=0) (h3 : v (3:K)=0) (h17 : v (17:K)=0) :
    0<f-5*a ∧ ((∀p∈inputs0 S w,(2*p.2.2:ℤ)≤v p.2.1) ∨
      (∀p∈inputs0 S w,(2*p.2.2:ℤ)≤v (conj p.2.1))) := by
  have hscale : A0 S w=((1:ℚ))^2 := by simp only [A0]; ring
  have ha : Even a := square_value_even (rational v) _ a (by rw [←hscale]; exact hA)
  obtain ⟨hR,hq1,hq4,hq13,hed⟩ := contact0_valuations S w source (rational v) a f hA hF hd ha hf
  have hw1 : v (q0_1 S w)=(-(f-5*a):ℤ) := by simpa [q0_1,q0,rational_apply] using hq1
  have hw4 : v (q0_4 S w)=(-7*(f-5*a):ℤ) := by simpa [q0_4,xx0,rational_apply] using hq4
  have hw13 : v (q0_13 S w)=(-25*(f-5*a):ℤ) := by simpa [q0_13,zz0,rational_apply] using hq13
  have hconj1 : conj (q0_1 S w)=q0_1 S w := by simp [q0_1]
  have hconj4 : conj (q0_4 S w)=q0_4 S w := by simp [q0_4]
  have hconj13 : conj (q0_13 S w)=q0_13 S w := by simp [q0_13]
  have he := all_even S w source v hD h2
  have hec := all_even S w source (v.comap conj)
    (by change v (conj (pair 11 6))=0; exact hDc)
    (by change v (conj (2:K))=0; rw [show conj (2:K)=2 by ext <;> norm_num [conj,pair]]; exact h2)
  obtain ⟨hterminal,hB⟩ := detector0_terminal S w source
  apply extract v (f-5*a) (inputs0 S w) (pair (ed0 S w) 0) (pair (w 189) 0) (pair (w 190) 0) hR
  · intro p hp
    simp only [inputs0,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa using hw4
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw4
    · simpa using hw13
    · simpa using hw13
    · simpa using hw13
    · simpa using hw4
    · simpa using hw13
  · intro p hp
    simp only [inputs0,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa only [hconj4] using (show v (q0_4 S w)=(-(2*4-1)*(f-5*a):ℤ) by simpa using hw4)
    · simpa only [hconj1] using (show v (q0_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q0_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q0_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q0_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q0_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q0_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q0_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q0_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q0_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj4] using (show v (q0_4 S w)=(-(2*4-1)*(f-5*a):ℤ) by simpa using hw4)
    · simpa only [hconj13] using (show v (q0_13 S w)=(-(2*13-1)*(f-5*a):ℤ) by simpa using hw13)
    · simpa only [hconj13] using (show v (q0_13 S w)=(-(2*13-1)*(f-5*a):ℤ) by simpa using hw13)
    · simpa only [hconj13] using (show v (q0_13 S w)=(-(2*13-1)*(f-5*a):ℤ) by simpa using hw13)
    · simpa only [hconj4] using (show v (q0_4 S w)=(-(2*4-1)*(f-5*a):ℤ) by simpa using hw4)
    · simpa only [hconj13] using (show v (q0_13 S w)=(-(2*13-1)*(f-5*a):ℤ) by simpa using hw13)
  · intro p hp
    simp only [inputs0,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact he.1
    · exact he.2.2.2.2.2.1
    · exact he.2.1
    · exact he.2.2.1
    · exact he.2.2.2.1
    · exact he.2.2.2.2.1
    · exact he.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · intro p hp
    simp only [inputs0,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact conj_even v _ (hec.1)
    · exact conj_even v _ (hec.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.1)
    · exact conj_even v _ (hec.2.2.1)
    · exact conj_even v _ (hec.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  · intro p hp
    simp only [inputs0,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · exact hed
  · rw [eval0_actual S w source]
    simpa [node0_15,conj_pair] using ConcreteValuationTrace.source_trace_equation (w 187) (w 188) (w 189) (by simpa using hterminal)
  · have hh : (w 190)*(ed0 S w)=(w 189)^2 := by simpa [ed0] using hB
    ext <;> simp [pair,pow_two] <;> nlinarith [hh]
  · intro b hb ho
    exact RawSourcePole318.detector0_no_negative_odd S w source (rational v) b hb ho h17 h3

@[expose] def inputs1 (S : ℚ) (w : Assignment) : List (K×K×ℤ) := [(q1_4 S w,leaf0 S w,4), (q1_1 S w,leaf5 S w,1), (q1_1 S w,leaf1 S w,1), (q1_1 S w,leaf2 S w,1), (q1_1 S w,leaf3 S w,1), (q1_1 S w,leaf4 S w,1), (q1_1 S w,leaf6 S w,1), (q1_1 S w,leaf7 S w,1), (q1_1 S w,leaf8 S w,1), (q1_1 S w,leaf9 S w,1), (q1_4 S w,leaf10 S w,4), (q1_13 S w,leaf11 S w,13), (q1_13 S w,leaf12 S w,13), (q1_13 S w,leaf13 S w,13), (q1_4 S w,leaf14 S w,4), (q1_13 S w,leaf15 S w,13)]
theorem eval1_actual (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    eval 1 (inputs1 S w)=node1_15 S w := by
  rw [eval_forget]
  have heq : (inputs1 S w).map (fun p=>(p.1,p.2.1))=detector1_leaves S w := rfl
  rw [heq]
  exact detector1_actual S w source

theorem contact1_extract (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (a f : ℤ)
    (hA : rational v (A1 S w)=a) (hF : rational v (F1 S w)=f)
    (hd : rational v (delta1 S w)=0) (hf : Odd f)
    (hD : v (pair 11 6)=0) (hDc : v (pair 11 (-6))=0)
    (h2 : v (2:K)=0) (h3 : v (3:K)=0) (h17 : v (17:K)=0) :
    0<f-5*a ∧ ((∀p∈inputs1 S w,(2*p.2.2:ℤ)≤v p.2.1) ∨
      (∀p∈inputs1 S w,(2*p.2.2:ℤ)≤v (conj p.2.1))) := by
  have hscale : A1 S w=(w 143+w 145)^2 := by simp only [A1]; ring
  have ha : Even a := square_value_even (rational v) _ a (by rw [←hscale]; exact hA)
  obtain ⟨hR,hq1,hq4,hq13,hed⟩ := contact1_valuations S w source (rational v) a f hA hF hd ha hf
  have hw1 : v (q1_1 S w)=(-(f-5*a):ℤ) := by simpa [q1_1,q1,rational_apply] using hq1
  have hw4 : v (q1_4 S w)=(-7*(f-5*a):ℤ) := by simpa [q1_4,xx1,rational_apply] using hq4
  have hw13 : v (q1_13 S w)=(-25*(f-5*a):ℤ) := by simpa [q1_13,zz1,rational_apply] using hq13
  have hconj1 : conj (q1_1 S w)=q1_1 S w := by simp [q1_1]
  have hconj4 : conj (q1_4 S w)=q1_4 S w := by simp [q1_4]
  have hconj13 : conj (q1_13 S w)=q1_13 S w := by simp [q1_13]
  have he := all_even S w source v hD h2
  have hec := all_even S w source (v.comap conj)
    (by change v (conj (pair 11 6))=0; exact hDc)
    (by change v (conj (2:K))=0; rw [show conj (2:K)=2 by ext <;> norm_num [conj,pair]]; exact h2)
  obtain ⟨hterminal,hB⟩ := detector1_terminal S w source
  apply extract v (f-5*a) (inputs1 S w) (pair (ed1 S w) 0) (pair (w 240) 0) (pair (w 241) 0) hR
  · intro p hp
    simp only [inputs1,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa using hw4
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw4
    · simpa using hw13
    · simpa using hw13
    · simpa using hw13
    · simpa using hw4
    · simpa using hw13
  · intro p hp
    simp only [inputs1,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa only [hconj4] using (show v (q1_4 S w)=(-(2*4-1)*(f-5*a):ℤ) by simpa using hw4)
    · simpa only [hconj1] using (show v (q1_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q1_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q1_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q1_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q1_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q1_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q1_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q1_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q1_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj4] using (show v (q1_4 S w)=(-(2*4-1)*(f-5*a):ℤ) by simpa using hw4)
    · simpa only [hconj13] using (show v (q1_13 S w)=(-(2*13-1)*(f-5*a):ℤ) by simpa using hw13)
    · simpa only [hconj13] using (show v (q1_13 S w)=(-(2*13-1)*(f-5*a):ℤ) by simpa using hw13)
    · simpa only [hconj13] using (show v (q1_13 S w)=(-(2*13-1)*(f-5*a):ℤ) by simpa using hw13)
    · simpa only [hconj4] using (show v (q1_4 S w)=(-(2*4-1)*(f-5*a):ℤ) by simpa using hw4)
    · simpa only [hconj13] using (show v (q1_13 S w)=(-(2*13-1)*(f-5*a):ℤ) by simpa using hw13)
  · intro p hp
    simp only [inputs1,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact he.1
    · exact he.2.2.2.2.2.1
    · exact he.2.1
    · exact he.2.2.1
    · exact he.2.2.2.1
    · exact he.2.2.2.2.1
    · exact he.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · intro p hp
    simp only [inputs1,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact conj_even v _ (hec.1)
    · exact conj_even v _ (hec.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.1)
    · exact conj_even v _ (hec.2.2.1)
    · exact conj_even v _ (hec.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  · intro p hp
    simp only [inputs1,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · exact hed
  · rw [eval1_actual S w source]
    simpa [node1_15,conj_pair] using ConcreteValuationTrace.source_trace_equation (w 238) (w 239) (w 240) (by simpa using hterminal)
  · have hh : (w 241)*(ed1 S w)=(w 240)^2 := by simpa [ed1] using hB
    ext <;> simp [pair,pow_two] <;> nlinarith [hh]
  · intro b hb ho
    exact RawSourcePole318.detector1_no_negative_odd S w source (rational v) b hb ho h17 h3

@[expose] def inputs2 (S : ℚ) (w : Assignment) : List (K×K×ℤ) := [(q2_4 S w,leaf0 S w,4), (q2_1 S w,leaf5 S w,1), (q2_1 S w,leaf1 S w,1), (q2_1 S w,leaf2 S w,1), (q2_1 S w,leaf3 S w,1), (q2_1 S w,leaf4 S w,1), (q2_1 S w,leaf6 S w,1), (q2_1 S w,leaf7 S w,1), (q2_1 S w,leaf8 S w,1), (q2_1 S w,leaf9 S w,1), (q2_4 S w,leaf10 S w,4), (q2_13 S w,leaf11 S w,13), (q2_13 S w,leaf12 S w,13), (q2_13 S w,leaf13 S w,13), (q2_4 S w,leaf14 S w,4), (q2_13 S w,leaf15 S w,13)]
theorem eval2_actual (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    eval 1 (inputs2 S w)=node2_15 S w := by
  rw [eval_forget]
  have heq : (inputs2 S w).map (fun p=>(p.1,p.2.1))=detector2_leaves S w := rfl
  rw [heq]
  exact detector2_actual S w source

theorem contact2_extract (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation K (WithTop ℤ)) (a f : ℤ)
    (hA : rational v (A2 S w)=a) (hF : rational v (F2 S w)=f)
    (hd : rational v (delta2 S w)=0) (hf : Odd f)
    (hD : v (pair 11 6)=0) (hDc : v (pair 11 (-6))=0)
    (h2 : v (2:K)=0) (h3 : v (3:K)=0) (h17 : v (17:K)=0) :
    0<f-5*a ∧ ((∀p∈inputs2 S w,(2*p.2.2:ℤ)≤v p.2.1) ∨
      (∀p∈inputs2 S w,(2*p.2.2:ℤ)≤v (conj p.2.1))) := by
  have hscale : A2 S w=(w 145)^2 := by simp only [A2]; ring
  have ha : Even a := square_value_even (rational v) _ a (by rw [←hscale]; exact hA)
  obtain ⟨hR,hq1,hq4,hq13,hed⟩ := contact2_valuations S w source (rational v) a f hA hF hd ha hf
  have hw1 : v (q2_1 S w)=(-(f-5*a):ℤ) := by simpa [q2_1,q2,rational_apply] using hq1
  have hw4 : v (q2_4 S w)=(-7*(f-5*a):ℤ) := by simpa [q2_4,xx2,rational_apply] using hq4
  have hw13 : v (q2_13 S w)=(-25*(f-5*a):ℤ) := by simpa [q2_13,zz2,rational_apply] using hq13
  have hconj1 : conj (q2_1 S w)=q2_1 S w := by simp [q2_1]
  have hconj4 : conj (q2_4 S w)=q2_4 S w := by simp [q2_4]
  have hconj13 : conj (q2_13 S w)=q2_13 S w := by simp [q2_13]
  have he := all_even S w source v hD h2
  have hec := all_even S w source (v.comap conj)
    (by change v (conj (pair 11 6))=0; exact hDc)
    (by change v (conj (2:K))=0; rw [show conj (2:K)=2 by ext <;> norm_num [conj,pair]]; exact h2)
  obtain ⟨hterminal,hB⟩ := detector2_terminal S w source
  apply extract v (f-5*a) (inputs2 S w) (pair (ed2 S w) 0) (pair (w 291) 0) (pair (w 292) 0) hR
  · intro p hp
    simp only [inputs2,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa using hw4
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw1
    · simpa using hw4
    · simpa using hw13
    · simpa using hw13
    · simpa using hw13
    · simpa using hw4
    · simpa using hw13
  · intro p hp
    simp only [inputs2,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa only [hconj4] using (show v (q2_4 S w)=(-(2*4-1)*(f-5*a):ℤ) by simpa using hw4)
    · simpa only [hconj1] using (show v (q2_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q2_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q2_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q2_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q2_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q2_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q2_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q2_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj1] using (show v (q2_1 S w)=(-(2*1-1)*(f-5*a):ℤ) by simpa using hw1)
    · simpa only [hconj4] using (show v (q2_4 S w)=(-(2*4-1)*(f-5*a):ℤ) by simpa using hw4)
    · simpa only [hconj13] using (show v (q2_13 S w)=(-(2*13-1)*(f-5*a):ℤ) by simpa using hw13)
    · simpa only [hconj13] using (show v (q2_13 S w)=(-(2*13-1)*(f-5*a):ℤ) by simpa using hw13)
    · simpa only [hconj13] using (show v (q2_13 S w)=(-(2*13-1)*(f-5*a):ℤ) by simpa using hw13)
    · simpa only [hconj4] using (show v (q2_4 S w)=(-(2*4-1)*(f-5*a):ℤ) by simpa using hw4)
    · simpa only [hconj13] using (show v (q2_13 S w)=(-(2*13-1)*(f-5*a):ℤ) by simpa using hw13)
  · intro p hp
    simp only [inputs2,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact he.1
    · exact he.2.2.2.2.2.1
    · exact he.2.1
    · exact he.2.2.1
    · exact he.2.2.2.1
    · exact he.2.2.2.2.1
    · exact he.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · intro p hp
    simp only [inputs2,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact conj_even v _ (hec.1)
    · exact conj_even v _ (hec.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.1)
    · exact conj_even v _ (hec.2.2.1)
    · exact conj_even v _ (hec.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact conj_even v _ (hec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  · intro p hp
    simp only [inputs2,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · exact hed
  · rw [eval2_actual S w source]
    simpa [node2_15,conj_pair] using ConcreteValuationTrace.source_trace_equation (w 289) (w 290) (w 291) (by simpa using hterminal)
  · have hh : (w 292)*(ed2 S w)=(w 291)^2 := by simpa [ed2] using hB
    ext <;> simp [pair,pow_two] <;> nlinarith [hh]
  · intro b hb ho
    exact RawSourcePole318.detector2_no_negative_odd S w source (rational v) b hb ho h17 h3

end SourceContact318
