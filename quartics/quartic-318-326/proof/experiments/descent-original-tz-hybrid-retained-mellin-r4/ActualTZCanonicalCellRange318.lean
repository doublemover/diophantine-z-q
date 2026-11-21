module
public import ActualTZContiguousFinInterval318
public import ActualTZRetainedHorizon318
import all ActualTZCanonicalWrapFibres318
public section
noncomputable section
namespace ActualTZCanonicalCellRange318
open scoped BigOperators
open ActualTZContiguousFinInterval318 ActualTZCanonicalWrapFibres318 ActualTZRetainedHorizon318

variable {I : Type*} [Fintype I] {n C : ℕ}
variable (hn : 0<n) (a : I→ℤ) (hCap : ∀ i,|a i|≤(C:ℤ)*(n:ℤ))
variable (r : Wrap I C)

theorem window_exists : Nonempty (Window (fibre (key n C hn a hCap) r)) := by
  apply exists_window
  intro l u x hl hu hxl hxu
  apply (interval_fibre hn a hCap r x).2
  have hL := (interval_fibre hn a hCap r l).1 hl
  have hU := (interval_fibre hn a hCap r u).1 hu
  have h₁ : (l.val:ℤ)≤x.val := by exact_mod_cast (show l.val≤x.val from hxl)
  have h₂ : (x.val:ℤ)≤u.val := by exact_mod_cast (show x.val≤u.val from hxu)
  intro i
  exact ⟨(hL i).1.trans (add_le_add_right h₁ _),
    (add_le_add_right h₂ _).trans_lt (hU i).2⟩

/-- Exact affine representative for any original x in the one
canonical wrap cell. This remains valid on both interval ends and
for negative shifts, with no independent x introduced. -/
theorem residue_eq (x : Fin n) (hx : x∈fibre (key n C hn a hCap) r) (i : I) :
    residue n ((x.val:ℤ)+1+a i)=(x.val:ℤ)+1+(a i-decode C r i*(n:ℤ)) := by
  have hk : key n C hn a hCap x=r := (Finset.mem_filter.mp hx).2
  have hq := decode_key n C hn a hCap x i
  rw [hk] at hq
  rw [residue_split,←hq]
  ring

theorem positive_site (W : ℕ) (hW : 0<W) (b : I→ℕ) (hb : ∀ i,1≤b i)
    (V : Window (fibre (key n C hn a hCap) r)) (t : ℕ) (ht : t<V.width) (i : I) :
    0<(W:ℤ)*(((V.start:ℤ)+1+(t:ℤ))+(a i-decode C r i*(n:ℤ)))+(b i:ℤ) := by
  let x := V.coord t ht
  have H := residue_eq hn a hCap r x (V.coord_mem t ht) i
  have hs : ((V.start:ℤ)+1+(t:ℤ))=(x.val:ℤ)+1 := by
    change ((V.start:ℤ)+1+(t:ℤ))=(↑(V.start+t):ℤ)+1
    push_cast
    ring
  rw [hs,←H]
  have hr := (residue_range n hn ((x.val:ℤ)+1+a i)).1
  have hWz : (0:ℤ)<W := by exact_mod_cast hW
  have hbz : (0:ℤ)<b i := by exact_mod_cast (show 0<b i by have h:=hb i; omega)
  exact add_pos (mul_pos hWz (zero_lt_one.trans_le hr)) hbz

/-- Every one of the original shared x's is counted exactly once;
zero-width keys stay in the enumerating family. -/
theorem sum_fibres {A : Type*} [AddCommMonoid A] (f : Fin n→Wrap I C) (F : Fin n→A) :
    (∑ r : Wrap I C,∑ x∈fibre f r,F x)=∑ x : Fin n,F x := by
  classical
  simp only [fibre,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

end ActualTZCanonicalCellRange318
