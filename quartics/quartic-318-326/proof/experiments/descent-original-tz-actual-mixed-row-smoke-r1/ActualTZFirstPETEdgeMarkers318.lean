module
public import Mathlib
public section
noncomputable section
namespace ActualTZFirstPETEdgeMarkers318

/-- The ordinary envelope after the first pivot, on the same old x:
the pivot once, each remaining site in each of the two fine copies.
Tagging is preserved when a ν+1 expansion takes an arbitrary subset. -/
abbrev Slot (I : Type*) := Unit ⊕ (Bool×I)

variable {I : Type*}

@[expose] def topTag (d : I→ℤ) (d₀ : ℤ) (e : Bool) : Slot I→ℤ
  | .inl _=>0
  | .inr (b,i)=>if b=e then d i-d₀ else 0

/-- This deliberately stores only the genuine first PET row. The
common physical factor W is not normalized away. The side block
translation s may be as large as the coarse length M₀. -/
@[expose] def offset (W d₀ s : ℤ) (d ℓ c : I→ℤ) (h : Bool→ℤ) : Slot I→ℤ
  | .inl _=>0
  | .inr (e,i)=>(d i-d₀)*W*(s+h e)^2+ℓ i*(s+h e)+c i

@[expose] def qprobe (f : (Bool→ℤ)→ℤ) (e : Bool) : ℤ :=
  f (fun t=>if t=e then 1 else 0)+f (fun t=>if t=e then -1 else 0)-2*f (fun _=>0)

theorem offset_probe (W d₀ s : ℤ) (d ℓ c : I→ℤ) (u : Slot I) (e : Bool) :
    qprobe (fun h=>offset W d₀ s d ℓ c h u) e=2*W*topTag d d₀ e u := by
  rcases u with _|⟨t,i⟩
  · simp only [qprobe,offset,topTag,mul_zero,add_zero,sub_zero]
  · by_cases he : t=e <;> simp only [qprobe,offset,topTag,he,if_pos,if_neg,add_zero] <;> ring

theorem distinguishes (d : I→ℤ) (d₀ : ℤ) (hD : Function.Injective d)
    (h₀ : ∀ i,d i≠d₀) (u v : Slot I) (hne : u≠v) :
    ∃ e : Bool,topTag d d₀ e u≠topTag d d₀ e v := by
  rcases u with u|⟨e,i⟩ <;> rcases v with v|⟨f,j⟩
  · exact (hne (congrArg Sum.inl (Subsingleton.elim _ _))).elim
  · refine ⟨f,?_⟩
    simp only [topTag,if_pos (rfl : f=f)]
    exact fun h=>h₀ j (sub_eq_zero.mp h.symm)
  · refine ⟨e,?_⟩
    simp only [topTag,if_pos (rfl : e=e)]
    exact fun h=>h₀ i (sub_eq_zero.mp h)
  · by_cases h : e=f
    · subst f
      refine ⟨e,?_⟩
      simp only [topTag,if_pos (rfl : e=e)]
      intro H
      have hij : i=j := hD (by omega)
      exact hne (by rw [hij])
    · have h' : f≠e := fun hf=>h hf.symm
      exact ⟨e,by
        simp only [topTag,if_pos (rfl : e=e),if_neg h']
        exact fun H=>h₀ i (sub_eq_zero.mp H)⟩

/-- After any wrap vector, phase origin, and side block, the actual
physical difference keeps the named top marker. The signed
interior endpoints y_i are not independently shifted. -/
theorem physical_probe (W d₀ s : ℤ) (d ℓ c : I→ℤ) (b wrap : Slot I→ℤ)
    (x n : ℤ) (u v : Slot I) (e : Bool) :
    qprobe (fun h=>
      (W*(x+offset W d₀ s d ℓ c h u-wrap u*n)+b u)-
        (W*(x+offset W d₀ s d ℓ c h v-wrap v*n)+b v)) e =
      2*W^2*(topTag d d₀ e u-topTag d d₀ e v) := by
  have hu := offset_probe W d₀ s d ℓ c u e
  have hv := offset_probe W d₀ s d ℓ c v e
  unfold qprobe at hu hv ⊢
  calc
    _ = W*((offset W d₀ s d ℓ c (fun t=>if t=e then 1 else 0) u+
        offset W d₀ s d ℓ c (fun t=>if t=e then -1 else 0) u-2*offset W d₀ s d ℓ c (fun _=>0) u)-
      (offset W d₀ s d ℓ c (fun t=>if t=e then 1 else 0) v+
        offset W d₀ s d ℓ c (fun t=>if t=e then -1 else 0) v-2*offset W d₀ s d ℓ c (fun _=>0) v)) := by ring
    _ = _ := by rw [hu,hv]; ring

/-- The edge offset cap is bounded despite the macroscopic translation
s=L in the end strip. It is proved from evaluation at s+h≤2L,
not by incorrectly bounding polynomial constants after translation. -/
theorem offset_cap (W d₀ s B C L n : ℤ) (d ℓ c : I→ℤ) (h : Bool→ℤ)
    (hB : 0≤B) (hW : 0≤W) (hL : 1≤L) (hN : W*L^2≤C*n)
    (hS : ∀ e,|s+h e|≤2*L)
    (hA : ∀ i,|(d i-d₀)*W|≤B*W) (hℓ : ∀ i,|ℓ i|≤B*W) (hc : ∀ i,|c i|≤B*W)
    (u : Slot I) : |offset W d₀ s d ℓ c h u|≤7*B*C*n := by
  have hL₀ : 0≤L := by omega
  have hBW : 0≤B*W := mul_nonneg hB hW
  have hC : 0≤7*B*C*n := by
    have H := mul_le_mul_of_nonneg_left hN (show 0≤7*B by positivity)
    nlinarith only [H,mul_nonneg hBW (sq_nonneg L)]
  rcases u with _|⟨e,i⟩
  · simpa only [offset,abs_zero] using hC
  · let u0 := s+h e
    have hSq : u0^2≤(2*L)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg u0) (hS e) 2
    have hT : |(d i-d₀)*W*u0^2|≤(B*W)*(2*L)^2 := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (hA i) hSq (sq_nonneg _) hBW
    have hLin : |ℓ i*u0|≤(B*W)*(2*L) := by
      rw [abs_mul]
      exact mul_le_mul (hℓ i) (hS e) (abs_nonneg _) hBW
    have hSqL : L≤L^2 := by
      have H := mul_le_mul_of_nonneg_right hL hL₀
      nlinarith only [H]
    have hl' : (2*L)^2+2*L+1≤7*L^2 := by nlinarith only [hL,hSqL]
    change |(d i-d₀)*W*u0^2+ℓ i*u0+c i|≤_
    calc
      _ ≤ |(d i-d₀)*W*u0^2|+|ℓ i*u0|+|c i| :=
        (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
      _ ≤ (B*W)*(2*L)^2+(B*W)*(2*L)+B*W := add_le_add (add_le_add hT hLin) (hc i)
      _ = (B*W)*((2*L)^2+2*L+1) := by ring
      _ ≤ (B*W)*(7*L^2) := mul_le_mul_of_nonneg_left hl' hBW
      _ = (7*B)*(W*L^2) := by ring
      _ ≤ (7*B)*(C*n) := mul_le_mul_of_nonneg_left hN (by positivity)
      _ = _ := by ring

end ActualTZFirstPETEdgeMarkers318
