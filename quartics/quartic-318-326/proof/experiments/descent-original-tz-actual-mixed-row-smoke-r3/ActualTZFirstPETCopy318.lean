module
public import Mathlib
public section
noncomputable section
namespace ActualTZFirstPETCopy318
open scoped BigOperators

/-- One coarse coordinate and the old fine coordinates. The
quadratic coefficient table is ordered with the original upper
triangle convention, so there is no hidden factor of 2. -/
structure Table (H : Type*) where
  top : ℤ
  pureSlope : ℤ
  mixed : H→ℤ
  constTerm : ℤ
  fineLin : H→ℤ
  fineQuad : H→H→ℤ

variable {H : Type*}

def eval [Fintype H] (Q : Table H) (m : ℤ) (h : H→ℤ) : ℤ :=
  Q.top*m^2+(Q.pureSlope+∑ i : H,Q.mixed i*h i)*m+
    Q.constTerm+(∑ i : H,Q.fineLin i*h i)+∑ i : H,∑ j : H,Q.fineQuad i j*h i*h j

def sub (P Q : Table H) : Table H where
  top := P.top-Q.top
  pureSlope := P.pureSlope-Q.pureSlope
  mixed i := P.mixed i-Q.mixed i
  constTerm := P.constTerm-Q.constTerm
  fineLin i := P.fineLin i-Q.fineLin i
  fineQuad i j := P.fineQuad i j-Q.fineQuad i j

theorem eval_sub [Fintype H] (P Q : Table H) (m : ℤ) (h : H→ℤ) :
    eval (sub P Q) m h=eval P m h-eval Q m h := by
  simp only [eval,sub,sub_mul,Finset.sum_sub_distrib]
  ring

/-- The two fresh fine variables are independent even after a
pivot is removed. e only selects which copy's variable enters. -/
def copy (Q : Table H) (e : Bool) : Table (H⊕Bool) where
  top := Q.top
  pureSlope := Q.pureSlope
  mixed
    | .inl i=>Q.mixed i
    | .inr t=>if t=e then 2*Q.top else 0
  constTerm := Q.constTerm
  fineLin
    | .inl i=>Q.fineLin i
    | .inr t=>if t=e then Q.pureSlope else 0
  fineQuad
    | .inl i,.inl j=>Q.fineQuad i j
    | .inl i,.inr t=>if t=e then Q.mixed i else 0
    | .inr _,.inl _=>0
    | .inr t,.inr u=>if t=e ∧ u=e then Q.top else 0

theorem eval_copy [Fintype H] (Q : Table H) (e : Bool) (m : ℤ) (h : H⊕Bool→ℤ) :
    eval (copy Q e) m h=eval Q (m+h (.inr e)) (fun i=>h (.inl i)) := by
  cases e <;>
    simp only [eval,copy,Fintype.sum_sum_type,Fintype.sum_bool,
      Bool.false_eq_true,Bool.true_eq_false,eq_self,if_true,if_false,true_and,false_and,and_true,and_false,
      mul_zero,zero_mul,add_zero,zero_add,Finset.sum_const_zero,add_mul,Finset.sum_add_distrib,
      ←Finset.sum_mul] <;> ring

structure Bound (Q : Table H) (B : ℤ) : Prop where
  nn : 0≤B
  top : |Q.top|≤B
  slope : |Q.pureSlope|≤B
  mixed : ∀ i,|Q.mixed i|≤B
  floor : |Q.constTerm|≤B
  fineLin : ∀ i,|Q.fineLin i|≤B
  fineQuad : ∀ i j,|Q.fineQuad i j|≤B

private theorem sub_le (a b B : ℤ) (ha : |a|≤B) (hb : |b|≤B) : |a-b|≤2*B :=
  (abs_sub _ _).trans (by linarith only [ha,hb])

theorem sub_bound (P Q : Table H) (B : ℤ) (hP : Bound P B) (hQ : Bound Q B) :
    Bound (sub P Q) (2*B) :=
  ⟨mul_nonneg (by norm_num) hP.nn,sub_le _ _ _ hP.top hQ.top,sub_le _ _ _ hP.slope hQ.slope,
    (fun i=>sub_le _ _ _ (hP.mixed i) (hQ.mixed i)),sub_le _ _ _ hP.floor hQ.floor,
    (fun i=>sub_le _ _ _ (hP.fineLin i) (hQ.fineLin i)),
    (fun i j=>sub_le _ _ _ (hP.fineQuad i j) (hQ.fineQuad i j))⟩

theorem copy_bound (Q : Table H) (B : ℤ) (hQ : Bound Q B) (e : Bool) :
    Bound (copy Q e) (2*B) := by
  have hB : B≤2*B := by have h:=hQ.nn; omega
  have hB₀ : 0≤2*B := hQ.nn.trans hB
  refine ⟨hB₀,hQ.top.trans hB,hQ.slope.trans hB,?_,hQ.floor.trans hB,?_,?_⟩
  · intro i
    cases i with
    | inl i => exact (hQ.mixed i).trans hB
    | inr t =>
      change |if t=e then 2*Q.top else 0|≤_
      split_ifs
      · rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℤ)≤2)]
        exact mul_le_mul_of_nonneg_left hQ.top (by norm_num)
      · simpa only [abs_zero] using hB₀
  · intro i
    cases i with
    | inl i => exact (hQ.fineLin i).trans hB
    | inr t =>
      change |if t=e then Q.pureSlope else 0|≤_
      split_ifs
      · exact hQ.slope.trans hB
      · simpa only [abs_zero] using hB₀
  · intro i j
    cases i <;> cases j <;> simp only [copy]
    · exact (hQ.fineQuad _ _).trans hB
    · split_ifs
      · exact (hQ.mixed _).trans hB
      · simpa only [abs_zero] using hB₀
    · simpa only [abs_zero] using hB₀
    · split_ifs
      · exact hQ.top.trans hB
      · simpa only [abs_zero] using hB₀

/-- Original quadratic input, or any peeled step at the same W.
Formal coefficient size grows by at most four for this exact
subtract/shift operation, not by a growing physical N power. -/
theorem next_bound (P pivot : Table H) (B W : ℤ) (hP : Bound P (B*W))
    (hPivot : Bound pivot (B*W)) (e : Bool) :
    Bound (copy (sub P pivot) e) ((4*B)*W) := by
  convert copy_bound (sub P pivot) (2*(B*W)) (sub_bound P pivot (B*W) hP hPivot) e using 1 <;> ring

/-- Same old node in both copied branches, after the same pivot
subtraction: q≠0 gives the exact nonzero fresh formal slope,
not an assertion that its integer value never vanishes. -/
theorem distinct_fresh_slopes (Q : Table H) (hq : Q.top≠0) :
    (copy Q false).mixed (.inr false)≠(copy Q true).mixed (.inr false) := by
  simp only [copy,if_pos (rfl : false=false),Bool.false_eq_true,if_false]
  exact mul_ne_zero (by norm_num) hq

end ActualTZFirstPETCopy318
