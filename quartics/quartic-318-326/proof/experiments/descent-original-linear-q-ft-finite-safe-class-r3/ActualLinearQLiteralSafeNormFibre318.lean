module
public import ActualA4FieldNormCount318
public section
noncomputable section
namespace ActualLinearQLiteralSafeNormFibre318

open scoped BigOperators
open Classical
open ActualA4FieldNormCount318

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def normSet (n : F) : Finset (F×F) :=
  Finset.univ.filter (fun x => x.1^2+x.2^2=n)

@[expose] def bad (n e : F) : Finset (F×F) :=
  (normSet n).filter (fun x => (x.1+e)^2+x.2^2=0)

@[expose] def safe (n : F) : Finset (F×F) :=
  normSet n \ (bad n (-1) ∪ bad n 1)

private def countEquiv (n : F) : ↥(normSet n) ≃ NormFiber n where
  toFun x := ⟨x.val,(Finset.mem_filter.mp x.prop).2⟩
  invFun x := ⟨x.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,x.prop⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem norm_size (hF : ringChar F ≠ 2) (h2 : (2:F) ≠ 0) {n : F} (hn : n ≠ 0) :
    ((normSet n).card:ℤ)=(Fintype.card F:ℤ)-quadraticChar F (-1:F) := by
  calc
    _ = (Nat.card ↥(normSet n):ℤ) := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = (Nat.card (NormFiber n):ℤ) :=
      congrArg (fun a : ℕ => (a:ℤ)) (Nat.card_congr (countEquiv n))
    _ = _ := norm_nonzero hF h2 n hn

private def roots (t : F) : Finset F :=
  Finset.univ.filter (fun b => b^2=t)

private theorem roots_card (t : F) : (roots t).card ≤ 2 := by
  by_cases h : ∃ b, b ∈ roots t
  · obtain ⟨b,hb⟩ := h
    have hb' : b^2=t := (Finset.mem_filter.mp hb).2
    have hs : roots t ⊆ {b,-b} := by
      intro c hc
      have hc' : c^2=t := (Finset.mem_filter.mp hc).2
      have hz : (c-b)*(c+b)=0 := by linear_combination hc' - hb'
      rcases mul_eq_zero.mp hz with he|he
      · rw [sub_eq_zero.mp he]
        exact Finset.mem_insert_self _ _
      · have e : c= -b := by linear_combination he
        rw [e]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    exact (Finset.card_le_card hs).trans ((Finset.card_insert_le b ({-b}:Finset F)).trans_eq (by simp))
  · have he : roots t=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun b hb => h ⟨b,hb⟩)
    simp [he]

/-- Each shifted-norm-zero condition fixes ONE real coordinate on the
given norm fibre: 2 e a=−(n+1). Thus it removes at most two ordinate
classes, whether the Gaussian algebra at this prime splits or not. -/
theorem bad_card (n e : F) (h2 : (2:F) ≠ 0) (he : e^2=1) :
    (bad n e).card ≤ 2 := by
  have hE : e ≠ 0 := by intro hz; simp [hz] at he
  let a := -(n+1)/(2*e)
  have hA (x : F×F) (hx : x ∈ bad n e) : x.1=a := by
    have hN := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    have hB := (Finset.mem_filter.mp hx).2
    apply (eq_div_iff (mul_ne_zero h2 hE)).2
    linear_combination hB-hN-he
  have hmap : Set.MapsTo Prod.snd (bad n e : Set (F×F)) (roots (n-a^2) : Set F) := by
    intro x hx
    have hx' : x ∈ bad n e := hx
    have hN := (Finset.mem_filter.mp (Finset.mem_filter.mp hx').1).2
    rw [hA x hx'] at hN
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linear_combination hN⟩
  have hinj : Set.InjOn Prod.snd (bad n e : Set (F×F)) := by
    intro x hx y hy H
    exact Prod.ext ((hA x hx).trans (hA y hy).symm) H
  exact (Finset.card_le_card_of_injOn Prod.snd hmap hinj).trans (roots_card _)

theorem safe_count (hF : ringChar F ≠ 2) (h2 : (2:F) ≠ 0) {n : F} (hn : n ≠ 0) :
    (Fintype.card F:ℤ)-quadraticChar F (-1:F)-4 ≤ ((safe n).card:ℤ) := by
  have hSub : bad n (-1) ∪ bad n 1 ⊆ normSet n := by
    intro x hx
    rcases Finset.mem_union.mp hx with hm|hp
    · exact (Finset.mem_filter.mp hm).1
    · exact (Finset.mem_filter.mp hp).1
  have hminus := bad_card n (-1) h2 (by norm_num)
  have hplus := bad_card n 1 h2 (by norm_num)
  have hB : (bad n (-1) ∪ bad n 1).card ≤ 4 :=
    (Finset.card_union_le _ _).trans (by omega)
  have hc := Finset.card_sdiff_add_card_eq_card hSub
  change (safe n).card+(bad n (-1) ∪ bad n 1).card=(normSet n).card at hc
  have hC : ((safe n).card:ℤ)+((bad n (-1) ∪ bad n 1).card:ℤ)=((normSet n).card:ℤ) := by
    exact_mod_cast hc
  rw [norm_size hF h2 hn] at hC
  have hh : (((bad n (-1) ∪ bad n 1).card):ℤ) ≤ 4 := by exact_mod_cast hB
  omega

/-- The original Gaussian reference safety, literally pointwise
on both neighbors. Conditioning on one norm is retained. -/
theorem safe_iff (n : F) (x : F×F) : x ∈ safe n ↔
    x.1^2+x.2^2=n ∧ (x.1-1)^2+x.2^2≠0 ∧ (x.1+1)^2+x.2^2≠0 := by
  simp only [safe,Finset.mem_sdiff,bad,Finset.mem_union,Finset.mem_filter,normSet,Finset.mem_univ,true_and,
    sub_eq_add_neg]
  tauto

/-- Normalized safe Artin fibre, before multiplying components. A full
fibre cardinal remains in the denominator; using the group size of its
ambient ring, or a probability of an independent norm, is unnecessary. -/
theorem safe_fraction_lower (hF : ringChar F ≠ 2) (h2 : (2:F) ≠ 0) {n : F}
    (hn : n ≠ 0) (hN : 0 < (normSet n).card) :
    1 - 4/((normSet n).card:ℝ) ≤ ((safe n).card:ℝ)/((normSet n).card:ℝ) := by
  have hZ := safe_count hF h2 hn
  rw [←norm_size hF h2 hn] at hZ
  have hR : ((normSet n).card:ℝ)-4 ≤ ((safe n).card:ℝ) := by exact_mod_cast hZ
  have hP : (0:ℝ) < (normSet n).card := by exact_mod_cast hN
  calc
    _ = (((normSet n).card:ℝ)-4)/((normSet n).card:ℝ) := by
      rw [sub_div,div_self hP.ne']
    _ ≤ _ := div_le_div_of_nonneg_right hR hP.le

end ActualLinearQLiteralSafeNormFibre318
