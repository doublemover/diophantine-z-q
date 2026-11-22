module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic
public section
noncomputable section
namespace ActualBinaryElementaryCocycle318
open scoped BigOperators

abbrev B := ZMod 2
abbrev V (m:ℕ) := Fin m→B

def ei {m:ℕ} (i:Fin m):V m:=fun j=>if j=i then 1 else 0
lemma twice (x:B):x+x=0:=(show ∀ t:B,t+t=0 by decide) x
lemma bit (x:B):x=0 ∨ x=1:=(show ∀ t:B,t=0 ∨ t=1 by decide) x

structure Law {m:ℕ} (f:V m→V m→B) : Prop where
  left : ∀ x,f 0 x=0
  right : ∀ x,f x 0=0
  coc : ∀ x y z,f (x+y) z+f x y=f y z+f x (y+z)

def correction {m:ℕ} (f:V m→V m→B) (x y:V m):B:=
  ∑ i,∑ j,f (ei i) (ei j)*x i*y j

private lemma corr_add_left {m:ℕ} (f:V m→V m→B) (a b c:V m) :
    correction f (a+b) c=correction f a c+correction f b c := by
  simp only [correction,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]
private lemma corr_add_right {m:ℕ} (f:V m→V m→B) (a b c:V m) :
    correction f a (b+c)=correction f a b+correction f a c := by
  simp only [correction,Pi.add_apply,mul_add,Finset.sum_add_distrib]

private lemma corr_basis {m:ℕ} (f:V m→V m→B) (i j:Fin m) :
    correction f (ei i) (ei j)=f (ei i) (ei j) := by
  simp [correction,ei,mul_ite]

def residual {m:ℕ} (f:V m→V m→B) (x y:V m):B:=f x y-correction f x y

private lemma residualLaw {m:ℕ} (f:V m→V m→B) (h:Law f) : Law (residual f) where
  left x:=by simp [residual,correction,h.left]
  right x:=by simp [residual,correction,h.right]
  coc x y z:=by
    simp only [residual,corr_add_left,corr_add_right]
    rw [sub_add_sub_comm,h.coc]
    abel

private def commutator {m:ℕ} (f:V m→V m→B) (x y:V m):B:=f x y-f y x
private lemma comm_add_left {m:ℕ} (f:V m→V m→B) (h:Law f) (x y z:V m) :
    commutator f (x+y) z=commutator f x z+commutator f y z := by
  unfold commutator
  have a:=h.coc x y z
  have b:=h.coc z x y
  have c:=h.coc x z y
  rw [add_comm z x] at b
  rw [add_comm z y] at c
  linear_combination a+b-c

private lemma comm_add_right {m:ℕ} (f:V m→V m→B) (h:Law f) (x y z:V m) :
    commutator f x (y+z)=commutator f x y+commutator f x z := by
  calc
    _ = -commutator f (y+z) x := by simp only [commutator];abel
    _ = _ := by rw [comm_add_left _ h];simp only [commutator];abel

private lemma px {m:ℕ} (x:V m) : (∑ i,if x i=0 then (0:V m) else ei i)=x := by
  funext j
  rw [Finset.sum_apply]
  have single :
      (∑ i:Fin m,(if x i=0 then (0:V m) else ei i) j) =
      (if x j=0 then (0:V m) else ei j) j :=
    Finset.sum_eq_single j (fun i _ h=>by
      by_cases h0:x i=0
      · simp [h0]
      · simp [ei,h0,Ne.symm h]) (by simp)
  rw [single]
  rcases bit (x j) with h|h
  · simp [h]
  · simp [h,ei]

private lemma zero_if_basis {m:ℕ} (g:V m→B) (h0:g 0=0)
    (hadd:∀ a b,g (a+b)=g a+g b) (hb:∀ i,g (ei i)=0) (x:V m) : g x=0 := by
  let G:V m→+B:={ toFun:=g,map_zero':=h0,map_add':=hadd }
  change G x=0
  rw [←px x,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  split
  · exact h0
  · exact hb i

private lemma res_symm {m:ℕ} (f:V m→V m→B) (h:Law f) (x y:V m) :
    residual f x y=residual f y x := by
  let g:=residual f
  have H : Law g := residualLaw f h
  have v (i:Fin m) (y:V m):commutator g (ei i) y=0:=
    zero_if_basis (commutator g (ei i)) (by simp [commutator,H.left,H.right])
    (comm_add_right g H _) (by intro j;simp [commutator,g,residual,corr_basis]) y
  have all:=zero_if_basis (fun a=>commutator g a y) (by simp [commutator,H.left,H.right])
    (fun a b=>comm_add_left g H a b y) (fun i=>v i y) x
  exact sub_eq_zero.mp all

private lemma zz {m:ℕ} (x:V m) : x+x=0 := by funext i;exact twice (x i)

private lemma res_diag_add {m:ℕ} (f:V m→V m→B) (h:Law f) (x y:V m) :
    residual f (x+y) (x+y)=residual f x x+residual f y y := by
  let g:=residual f
  have H : Law g := residualLaw f h
  have a:=H.coc x y (x+y)
  rw [show y+(x+y)=x by rw [←add_assoc,add_comm y x,add_assoc,zz,add_zero]] at a
  have b:=H.coc y x y
  rw [add_comm y x] at b
  have c:=H.coc x y y
  rw [zz,H.right,add_zero] at c
  have e:g y x=g x y:=res_symm f h y x
  rw [e] at b
  have t:=twice (g x y)
  change g (x+y) (x+y)=g x x+g y y
  linear_combination a-b+c-t

private lemma res_diag {m:ℕ} (f:V m→V m→B) (h:Law f) (x:V m) :
    residual f x x=0 :=
  zero_if_basis (fun y=>residual f y y) ((residualLaw f h).left 0)
    (res_diag_add f h) (by intro i;simp [residual,corr_basis]) x

private structure Ext (m:ℕ) where
  fst : V m
  snd : B

private lemma extI {m:ℕ} {x y:Ext m} (a:x.fst=y.fst) (b:x.snd=y.snd) : x=y := by
  cases x
  cases y
  cases a
  cases b
  rfl

/-- An actual section of a central binary extension after its commutators
and squares are removed. This proves the cochain statement without assuming
any abstract group-cohomology computation. -/
theorem elementary_cup_decomposition {m:ℕ} (f:V m→V m→B) (h:Law f) :
    ∃ b:V m→B,∀ x y,f x y=correction f x y+(b y-b (x+y)+b x) := by
  let r:=residual f
  have Hr : Law r := residualLaw f h
  have rcomm (x y:V m):r x y=r y x:=res_symm f h x y
  have rdiag (x:V m):r x x=0:=res_diag f h x
  let E:=Ext m
  let op:E→E→E:=fun a b=>⟨a.1+b.1,a.2+b.2+r a.1 b.1⟩
  let e0:E:=⟨0,0⟩
  let N:ℕ→E→E:=fun k a=>Nat.rec e0 (fun _ b=>op b a) k
  let Z:ℤ→E→E:=fun k a=>match k with
    | .ofNat j=>N j a
    | .negSucc j=>N (j+1) a
  let : AddCommGroup E :=
    { add:=op
      zero:=e0
      neg:=id
      sub:=op
      sub_eq_add_neg:=fun _ _=>rfl
      add_assoc:=by
        intro a b c
        apply extI
        · exact add_assoc _ _ _
        · change (a.2+b.2+r a.1 b.1)+c.2+r (a.1+b.1) c.1=
            a.2+(b.2+c.2+r b.1 c.1)+r a.1 (b.1+c.1)
          linear_combination Hr.coc a.1 b.1 c.1
      zero_add:=by
        intro a
        apply extI (zero_add _)
        change 0+a.2+r 0 a.1=a.2
        rw [Hr.left,zero_add,add_zero]
      add_zero:=by
        intro a
        apply extI (add_zero _)
        change a.2+0+r a.1 0=a.2
        rw [Hr.right,add_zero,add_zero]
      neg_add_cancel:=by
        intro a
        apply extI (zz a.1)
        change a.2+a.2+r a.1 a.1=0
        rw [rdiag,twice,add_zero]
      add_comm:=by
        intro a b
        apply extI (add_comm _ _)
        change a.2+b.2+r a.1 b.1=b.2+a.2+r b.1 a.1
        rw [add_comm a.2 b.2,rcomm a.1 b.1]
      nsmul:=N
      nsmul_zero:=fun _=>rfl
      nsmul_succ:=fun _ _=>rfl
      zsmul:=Z
      zsmul_zero':=fun _=>rfl
      zsmul_succ':=fun _ _=>rfl
      zsmul_neg':=fun _ _=>rfl }
  let row (i:Fin m):B→+E:=
    { toFun:=fun t=>if t=0 then 0 else (⟨ei i,0⟩:E)
      map_zero':=by simp
      map_add':=by
        intro a b
        rcases bit a with rfl|rfl <;> rcases bit b with rfl|rfl
        · simp
        · simp
        · simp
        · rw [show (1:B)+1=0 by decide]
          change (if (0:B)=0 then (0:E) else (⟨ei i,0⟩:E))=(if (1:B)=0 then (0:E) else (⟨ei i,0⟩:E))+
            (if (1:B)=0 then (0:E) else (⟨ei i,0⟩:E))
          simp only [ite_true,one_ne_zero,ite_false]
          exact (extI (zz (ei i)) (by change (0:B)+0+r (ei i) (ei i)=0;rw [rdiag,add_zero,add_zero])).symm }
  let s:V m→+E:=∑ i,(row i).comp (Pi.evalAddMonoidHom _ i)
  let ev (x:V m):(V m→+E)→+E:=
    { toFun:=fun g=>g x,map_zero':=rfl,map_add':=fun _ _=>rfl }
  have s_val (x:V m):s x=∑ i,row i (x i):=by
    change ev x (∑ i,(row i).comp (Pi.evalAddMonoidHom _ i))=_
    rw [map_sum]
    rfl
  let fst:E→+V m:=⟨⟨Ext.fst,rfl⟩,fun _ _=>rfl⟩
  have fst_s (x:V m):(s x).1=x:=by
    change fst (s x)=x
    rw [s_val,map_sum]
    calc
      _ = ∑ i,if x i=0 then (0:V m) else ei i := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases a:x i=0
        · change fst (if x i=0 then 0 else (⟨ei i,0⟩:E))=_
          rw [ite_eq_left a,ite_eq_left a,map_zero]
        · change fst (if x i=0 then 0 else (⟨ei i,0⟩:E))=_
          rw [ite_eq_right a,ite_eq_right a]
          rfl
      _ = x := px x
  let b:V m→B:=fun x=>(s x).2
  refine ⟨b,?_⟩
  intro x y
  have S := congrArg Ext.snd (s.map_add x y)
  change b (x+y)=b x+b y+r (s x).1 (s y).1 at S
  rw [fst_s,fst_s] at S
  have e:=twice (r x y)
  dsimp only [r,residual] at S e
  linear_combination S+e

end ActualBinaryElementaryCocycle318
