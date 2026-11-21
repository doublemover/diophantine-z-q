module
public import ActualTZDegreeTwoAlgebra318
public import ActualTZProbeExceptionalWheel318
public section
noncomputable section
namespace ActualTZHybridGlobalLocalStencil318
open scoped BigOperators
open MvPolynomial (C X eval_C eval_X)
open ActualTZDegreeTwoAlgebra318 ActualTZProbeExceptionalWheel318

abbrev Axis (a t : ℕ) := Fin a ⊕ Fin t
abbrev Bits (a t : ℕ) := Axis a t→Bool
abbrev Coord (a t s : ℕ) := (Bool×Fin a) ⊕ (Fin t×(Fin s⊕Bool))
abbrev Poly (a t s : ℕ) := MvPolynomial (Coord a t s) ℤ
abbrev Vals (a t s : ℕ) := Coord a t s→ℤ
variable {a t s : ℕ}

@[expose] def linear (q : ℕ) (w : Bits a t) : Poly a t s :=
  ∑ i : Fin a,if w (.inl i) then
    C (q:ℤ)*(X (.inl (true,i))-X (.inl (false,i))) else 0

@[expose] def localSlope (A : Fin s→ℤ) (u : Fin t) : Poly a t s :=
  ∑ k : Fin s,C (A k)*X (.inr (u,.inl k))

@[expose] def quadratic (A : Fin s→ℤ) (w : Bits a t) : Poly a t s :=
  ∑ u : Fin t,if w (.inr u) then
    localSlope A u*(X (.inr (u,.inr true))-X (.inr (u,.inr false))) else 0

@[expose] def stencil (q : ℕ) (A : Fin s→ℤ) (w : Bits a t) : Poly a t s :=
  linear q w+quadratic A w

@[expose] def physical (W n q : ℕ) (A : Fin s→ℤ) (w v : Bits a t) (e f : ℤ) : Poly a t s :=
  C (W:ℤ)*(stencil q A w-stencil q A v-C ((e-f)*(n:ℤ)))

@[expose] def off (q : ℕ) (A : Fin s→ℤ) (w : Bits a t) (z : Vals a t s) : ℤ :=
  (∑ i : Fin a,if w (.inl i) then (q:ℤ)*(z (.inl (true,i))-z (.inl (false,i))) else 0)+
    ∑ u : Fin t,if w (.inr u) then
      (∑ k : Fin s,A k*z (.inr (u,.inl k)))*
        (z (.inr (u,.inr true))-z (.inr (u,.inr false))) else 0

theorem eval_stencil (q : ℕ) (A : Fin s→ℤ) (w : Bits a t) (z : Vals a t s) :
    MvPolynomial.eval z (stencil q A w)=off q A w z := by
  simp only [stencil,off,linear,quadratic,map_add,map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp only [map_mul,map_sub,eval_C,eval_X,map_zero]
  · apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp only [localSlope,map_sum,map_mul,map_sub,eval_C,eval_X,map_zero]

theorem eval_physical (W n q : ℕ) (A : Fin s→ℤ) (w v : Bits a t) (e f x b : ℤ)
    (z : Vals a t s) :
    MvPolynomial.eval z (physical W n q A w v e f)=
      ((W:ℤ)*(x+off q A w z-e*n)+b)-((W:ℤ)*(x+off q A v z-f*n)+b) := by
  simp only [physical,map_mul,map_sub,eval_C,eval_stencil]
  ring

private theorem stencil_degree (q : ℕ) (A : Fin s→ℤ) (w : Bits a t) :
    (stencil q A w).totalDegree≤2 := by
  unfold stencil
  apply addD
  · unfold linear
    apply sumD
    intro i _
    split_ifs
    · exact scaleD _ _ 2 (subD _ _ 2 ((varD _).trans (by decide)) ((varD _).trans (by decide)))
    · simp
  · unfold quadratic
    apply sumD
    intro i _
    split_ifs
    · exact mulD _ _ 1 1 (sumD _ _ 1 (fun k _=>scaleD _ _ 1 (varD _)))
        (subD _ _ 1 (varD _) (varD _))
    · simp

theorem degree (W n q : ℕ) (A : Fin s→ℤ) (w v : Bits a t) (e f : ℤ) :
    (physical W n q A w v e f).totalDegree≤2 :=
  scaleD _ _ 2 (subD _ _ 2 (subD _ _ 2 (stencil_degree _ _ _) (stencil_degree _ _ _)) (constD _ 2))

@[expose] def gNeedle (i : Fin a) : Vals a t s
  | .inl (b,j) => if j=i ∧ b=true then 1 else 0
  | .inr _ => 0

@[expose] def lNeedle (u : Fin t) (k : Fin s) : Vals a t s
  | .inl _ => 0
  | .inr (v,.inl j) => if v=u ∧ j=k then 1 else 0
  | .inr (v,.inr b) => if v=u ∧ b=true then 1 else 0

theorem off_zero (q : ℕ) (A : Fin s→ℤ) (w : Bits a t) :
    off q A w (fun _=>0)=0 := by
  simp [off]

theorem g_probe (q : ℕ) (A : Fin s→ℤ) (w : Bits a t) (i : Fin a) :
    off q A w (gNeedle i)=if w (.inl i) then (q:ℤ) else 0 := by
  have h : (∑ j : Fin a,if w (.inl j) then (q:ℤ)*
      (gNeedle (t:=t) (s:=s) i (.inl (true,j))-gNeedle (t:=t) (s:=s) i (.inl (false,j))) else 0)=
      if w (.inl i) then (q:ℤ) else 0 := by
    rw [Finset.sum_eq_single i]
    · simp [gNeedle]
    · intro j _ hj
      simp [gNeedle,hj]
    · simp
  unfold off
  rw [h]
  simp [gNeedle]

private theorem slope_probe (A : Fin s→ℤ) (u v : Fin t) (k : Fin s) :
    (∑ j,A j*lNeedle (a:=a) u k (.inr (v,.inl j)))=if v=u then A k else 0 := by
  by_cases h : v=u
  · rw [if_pos h,Finset.sum_eq_single k]
    · simp [lNeedle,h]
    · intro j _ hj; simp [lNeedle,h,hj]
    · simp
  · simp [lNeedle,h]

theorem l_probe (q : ℕ) (A : Fin s→ℤ) (w : Bits a t) (u : Fin t) (k : Fin s) :
    off q A w (lNeedle u k)=if w (.inr u) then A k else 0 := by
  have h0 : (∑ j : Fin a,if w (.inl j) then
      (q:ℤ)*(lNeedle (a:=a) u k (.inl (true,j))-
        lNeedle (a:=a) u k (.inl (false,j))) else 0)=0 := by
    simp only [lNeedle,sub_self,mul_zero,ite_self,Finset.sum_const_zero]
  unfold off
  rw [h0,zero_add,Finset.sum_eq_single u]
  · rw [slope_probe (a:=a) A u u k]
    simp [lNeedle]
  · intro v _ hv
    simp [lNeedle,hv]
  · simp

private theorem no_local_factor (W q p D : ℕ) (hp : p.Prime) (hD : D<p)
    (hP : ¬p∣W*q) (c : ℤ) (hc : c≠0) (hC : c.natAbs≤D) :
    ¬(p:ℤ)∣(W:ℤ)*((W:ℤ)*c) := by
  have hW : ¬p∣W := fun hd=>hP (dvd_mul_of_dvd_left hd _)
  have hcn : ¬p∣c.natAbs := by
    intro H
    have h0 := Int.natAbs_pos.mpr hc
    have hp' := Nat.le_of_dvd h0 H
    omega
  intro H
  have Hn : p∣((W:ℤ)*((W:ℤ)*c)).natAbs := by
    rw [←Int.natCast_dvd_natCast,Int.dvd_natAbs]
    exact H
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at Hn
  rcases hp.dvd_mul.1 Hn with hh|hh
  · exact hW hh
  rcases hp.dvd_mul.1 hh with hh|hh
  · exact hW hh
  · exact hcn hh

/-- Exact WQ hybrid coefficient marker, for any number of local
axes (only the first 0,1,2 are used in the rank-independent
analytic reduction). Fine coefficients are the ORIGINAL W
multiples, not new freely scaled slopes. -/
theorem survives (W n q p D : ℕ) (hp : p.Prime) (hD : D<p) (hP : ¬p∣W*q)
    (C₀ : Fin s→ℤ) (k : Fin s) (hk : C₀ k≠0) (hC : (C₀ k).natAbs≤D)
    (w v : Bits a t) (h : w≠v) (e f : ℤ) :
    MvPolynomial.map (Int.castRingHom (ZMod p))
      (physical W n q (fun i=>(W:ℤ)*C₀ i) w v e f)≠0 := by
  classical
  have he : ∃ z,w z≠v z := by
    by_contra! H
    exact h (funext H)
  obtain ⟨z,hz⟩ := he
  let A (i : Fin s) := (W:ℤ)*C₀ i
  have hG : ¬(p:ℤ)∣(W:ℤ)*(q:ℤ) := by exact_mod_cast hP
  have hL : ¬(p:ℤ)∣(W:ℤ)*A k := no_local_factor W q p D hp hD hP _ hk hC
  cases z with
  | inl i =>
    apply nonzero_from_probe p _ (gNeedle i) (fun _=>0)
    rw [eval_physical W n q A w v e f 0 0 (gNeedle i),
      eval_physical W n q A w v e f 0 0 (fun _=>0)]
    simp only [g_probe,off_zero]
    cases hw : w (.inl i) <;> cases hv : v (.inl i)
    · exact (hz (hw.trans hv.symm)).elim
    · simp only [hw,hv,Bool.false_eq_true,if_false,if_true]
      convert (fun hh=>hG (dvd_neg.mp hh) : ¬(p:ℤ)∣-((W:ℤ)*(q:ℤ))) using 1 <;> ring
    · simp only [hw,hv,Bool.false_eq_true,if_false,if_true]
      convert hG using 1 <;> ring
    · exact (hz (hw.trans hv.symm)).elim
  | inr u =>
    apply nonzero_from_probe p _ (lNeedle u k) (fun _=>0)
    rw [eval_physical W n q A w v e f 0 0 (lNeedle u k),
      eval_physical W n q A w v e f 0 0 (fun _=>0)]
    simp only [l_probe,off_zero]
    cases hw : w (.inr u) <;> cases hv : v (.inr u)
    · exact (hz (hw.trans hv.symm)).elim
    · simp only [hw,hv,Bool.false_eq_true,if_false,if_true]
      convert (fun hh=>hL (dvd_neg.mp hh) : ¬(p:ℤ)∣-((W:ℤ)*A k)) using 1 <;> ring
    · simp only [hw,hv,Bool.false_eq_true,if_false,if_true]
      convert hL using 1 <;> ring
    · exact (hz (hw.trans hv.symm)).elim

end ActualTZHybridGlobalLocalStencil318
