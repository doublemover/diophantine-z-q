module
public import Mathlib
public section
noncomputable section
namespace ActualTZCanonicalWrapFibres318
open scoped BigOperators
variable {I : Type*} [Fintype I]

@[expose] def residue (n : ℕ) (x : ℤ) : ℤ := 1+(x-1)%(n:ℤ)
@[expose] def quotient (n : ℕ) (x : ℤ) : ℤ := (x-1)/(n:ℤ)

theorem residue_split (n : ℕ) (x : ℤ) :
    residue n x=x-(n:ℤ)*quotient n x := by
  unfold residue quotient
  have H := Int.emod_add_ediv (x-1) (n:ℤ)
  linarith only [H]

theorem cell_iff (n : ℕ) (hn : 0<n) (x a r : ℤ) :
    quotient n (x+a)=r ↔ r*(n:ℤ)≤x+a-1 ∧ x+a-1<(r+1)*(n:ℤ) := by
  have hN : 0<(n:ℤ) := by exact_mod_cast hn
  unfold quotient
  constructor
  · intro e
    exact ⟨(Int.le_ediv_iff_mul_le hN).1 (by omega), (Int.ediv_lt_iff_lt_mul hN).1 (by omega)⟩
  · rintro ⟨hl,hu⟩
    have a := (Int.le_ediv_iff_mul_le hN).2 hl
    have b := (Int.ediv_lt_iff_lt_mul hN).2 hu
    omega

theorem quotient_bounds (n C : ℕ) (hn : 0<n) (x : Fin n) (a : ℤ)
    (ha : |a|≤(C:ℤ)*(n:ℤ)) :
    -(C:ℤ)≤quotient n ((x.val:ℤ)+1+a) ∧ quotient n ((x.val:ℤ)+1+a)≤(C:ℤ) := by
  have hN : 0<(n:ℤ) := by exact_mod_cast hn
  have hxL : (0:ℤ)≤x.val := by positivity
  have hxU : (x.val:ℤ)<n := by exact_mod_cast x.isLt
  obtain ⟨ha₁,ha₂⟩ := abs_le.mp ha
  unfold quotient
  constructor
  · apply (Int.le_ediv_iff_mul_le hN).2
    rw [neg_mul]
    omega
  · apply (Int.le_iff_lt_add_one).2
    apply (Int.ediv_lt_iff_lt_mul hN).2
    rw [add_mul,one_mul]
    omega

abbrev Wrap (I : Type*) (C : ℕ) := I→Fin (2*C+1)

def decode (C : ℕ) (r : Wrap I C) (i : I) : ℤ := (r i).val-(C:ℤ)

def key (n C : ℕ) (hn : 0<n) (a : I→ℤ)
    (hCap : ∀ i,|a i|≤(C:ℤ)*(n:ℤ)) (x : Fin n) : Wrap I C :=
  fun i=>⟨(quotient n ((x.val:ℤ)+1+a i)+(C:ℤ)).toNat,by
    have H := quotient_bounds n C hn x (a i) (hCap i)
    omega⟩

theorem decode_key (n C : ℕ) (hn : 0<n) (a : I→ℤ)
    (hCap : ∀ i,|a i|≤(C:ℤ)*(n:ℤ)) (x : Fin n) (i : I) :
    decode C (key n C hn a hCap x) i=quotient n ((x.val:ℤ)+1+a i) := by
  have H := quotient_bounds n C hn x (a i) (hCap i)
  unfold decode key
  dsimp only
  rw [Int.toNat_of_nonneg (by omega)]
  omega

theorem card_wrap (C : ℕ) : Fintype.card (Wrap I C)=(2*C+1)^Fintype.card I := by
  simp only [Wrap,Fintype.card_fun,Fintype.card_fin]

def fibre {n C : ℕ} (f : Fin n→Wrap I C) (r : Wrap I C) : Finset (Fin n) :=
  Finset.univ.filter (fun x=>f x=r)

theorem fibres_cover {n C : ℕ} (f : Fin n→Wrap I C) :
    (∑ r : Wrap I C,(fibre f r).card)=n := by
  classical
  have H (r : Wrap I C) :
      (fibre f r).card=∑ x : Fin n,if f x=r then 1 else 0 := by
    exact (Finset.sum_boole (fun x : Fin n=>f x=r) Finset.univ).symm
  simp only [H]
  rw [Finset.sum_comm]
  have h (x : Fin n) : (∑ r : Wrap I C,if f x=r then (1:ℕ) else 0)=1 := by simp
  simp only [h,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

theorem interval_fibre {n C : ℕ} (hn : 0<n) (a : I→ℤ)
    (hCap : ∀ i,|a i|≤(C:ℤ)*(n:ℤ)) (r : Wrap I C) (x : Fin n) :
    x∈fibre (key n C hn a hCap) r ↔ ∀ i,
      decode C r i*(n:ℤ)≤(x.val:ℤ)+a i ∧
      (x.val:ℤ)+a i<(decode C r i+1)*(n:ℤ) := by
  classical
  have q (i : I) : quotient n ((x.val:ℤ)+1+a i)=decode C r i ↔
    decode C r i*(n:ℤ)≤(x.val:ℤ)+a i ∧
    (x.val:ℤ)+a i<(decode C r i+1)*(n:ℤ) := by
    have e : (x.val:ℤ)+1+a i-1=(x.val:ℤ)+a i := by ring
    simpa only [e] using cell_iff n hn ((x.val:ℤ)+1) (a i) (decode C r i)
  constructor
  · intro hx i
    have h := (Finset.mem_filter.mp hx).2
    exact (q i).1 ((decode_key n C hn a hCap x i).symm.trans
      (congrArg (fun r=>decode C r i) h))
  · intro H
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    funext i
    apply Fin.ext
    have h := (decode_key n C hn a hCap x i).trans ((q i).2 (H i))
    unfold decode at h
    omega

end ActualTZCanonicalWrapFibres318
