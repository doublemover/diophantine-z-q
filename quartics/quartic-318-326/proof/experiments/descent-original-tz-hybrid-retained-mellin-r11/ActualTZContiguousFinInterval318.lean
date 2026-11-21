module
public import Mathlib
public section
noncomputable section
namespace ActualTZContiguousFinInterval318
open scoped BigOperators

/-- A cell is indexed by zero-based ordinates. The old physical
variable uses the corresponding positive representative. -/
structure Window {n : ℕ} (S : Finset (Fin n)) where
  start : ℕ
  width : ℕ
  top : start+width≤n
  mem_iff (x : Fin n) : x∈S ↔ start≤x.val ∧ x.val<start+width

theorem exists_window {n : ℕ} (S : Finset (Fin n))
    (hConv : ∀ l r x : Fin n, l ∈ S → r ∈ S → l ≤ x → x ≤ r → x ∈ S) :
    Nonempty (Window S) := by
  classical
  by_cases h : S.Nonempty
  · let l := S.min' h
    let r := S.max' h
    have hl : l∈S := S.min'_mem h
    have hr : r∈S := S.max'_mem h
    have hlr : l.val≤r.val := S.min'_le r hr
    have hv : l.val+(r.val+1-l.val)=r.val+1 := by omega
    refine ⟨⟨l.val,r.val+1-l.val,by rw [hv]; exact r.isLt,?_⟩⟩
    intro x
    rw [hv]
    constructor
    · intro hx
      have hL : l.val≤x.val := S.min'_le x hx
      have hU : x.val≤r.val := S.le_max' x hx
      omega
    · rintro ⟨hx,hy⟩
      exact hConv l r x hl hr hx (show x.val≤r.val by omega)
  · refine ⟨⟨0,0,by simp,?_⟩⟩
    intro x
    simp only [add_zero,Nat.not_lt_zero,and_false,iff_false]
    exact fun hx=>h ⟨x,hx⟩

namespace Window

variable {n : ℕ} {S : Finset (Fin n)} (V : Window S)

def coord (t : ℕ) (ht : t<V.width) : Fin n :=
  ⟨V.start+t,by have h:=V.top; omega⟩

theorem coord_mem (t : ℕ) (ht : t<V.width) : V.coord t ht∈S :=
  (V.mem_iff _).2 (show V.start≤V.start+t ∧ V.start+t<V.start+V.width by omega)

/-- Exact signed sum reindex, including the empty cell. The +1
occurs exactly once, after indexing the finite cyclic carrier. -/
theorem sum_eq {A : Type*} [AddCommMonoid A] (f : ℤ→A) :
    (∑ x∈S,f ((x.val:ℤ)+1)) =
      ∑ t∈Finset.range V.width,f ((V.start:ℤ)+1+(t:ℤ)) := by
  symm
  apply Finset.sum_bij (fun t ht=>V.coord t (Finset.mem_range.mp ht))
  · intro t ht
    exact V.coord_mem t (Finset.mem_range.mp ht)
  · intro t ht u hu H
    have h := congrArg Fin.val H
    change V.start+t=V.start+u at h
    omega
  · intro x hx
    obtain ⟨hl,hu⟩ := (V.mem_iff x).1 hx
    refine ⟨x.val-V.start,Finset.mem_range.mpr (by omega),?_⟩
    apply Fin.ext
    change V.start+(x.val-V.start)=x.val
    omega
  · intro t ht
    congr 1
    change (V.start:ℤ)+1+(t:ℤ)=((V.start+t:ℕ):ℤ)+1
    push_cast
    ring

theorem width_eq : V.width=S.card := by
  simpa using (V.sum_eq (A:=ℕ) (fun _=>1)).symm

end Window
end ActualTZContiguousFinInterval318
